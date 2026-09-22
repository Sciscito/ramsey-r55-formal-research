"""Shared fail-closed Windows path guards for the parameterized R34 pipeline."""

from __future__ import annotations

import os
import stat
import ctypes
import msvcrt
from contextlib import contextmanager
from ctypes import wintypes
from pathlib import Path, PureWindowsPath
from typing import BinaryIO, Iterator


class R34PathSafetyError(ValueError):
    """Raised when a path can escape or be redirected from the accepted S: tree."""


FileObjectIdentity = tuple[int, int]


class _BY_HANDLE_FILE_INFORMATION(ctypes.Structure):
    _fields_ = (
        ("dwFileAttributes", wintypes.DWORD),
        ("ftCreationTimeLow", wintypes.DWORD),
        ("ftCreationTimeHigh", wintypes.DWORD),
        ("ftLastAccessTimeLow", wintypes.DWORD),
        ("ftLastAccessTimeHigh", wintypes.DWORD),
        ("ftLastWriteTimeLow", wintypes.DWORD),
        ("ftLastWriteTimeHigh", wintypes.DWORD),
        ("dwVolumeSerialNumber", wintypes.DWORD),
        ("nFileSizeHigh", wintypes.DWORD),
        ("nFileSizeLow", wintypes.DWORD),
        ("nNumberOfLinks", wintypes.DWORD),
        ("nFileIndexHigh", wintypes.DWORD),
        ("nFileIndexLow", wintypes.DWORD),
    )


def _configured_kernel32() -> object:
    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    kernel32.CreateFileW.argtypes = (
        wintypes.LPCWSTR,
        wintypes.DWORD,
        wintypes.DWORD,
        ctypes.c_void_p,
        wintypes.DWORD,
        wintypes.DWORD,
        wintypes.HANDLE,
    )
    kernel32.CreateFileW.restype = wintypes.HANDLE
    kernel32.GetFileInformationByHandle.argtypes = (
        wintypes.HANDLE,
        ctypes.POINTER(_BY_HANDLE_FILE_INFORMATION),
    )
    kernel32.GetFileInformationByHandle.restype = wintypes.BOOL
    kernel32.CloseHandle.argtypes = (wintypes.HANDLE,)
    kernel32.CloseHandle.restype = wintypes.BOOL
    return kernel32


def _regular_identity_from_handle(
    kernel32: object, handle: int, path: Path
) -> FileObjectIdentity:
    information = _BY_HANDLE_FILE_INFORMATION()
    if not kernel32.GetFileInformationByHandle(  # type: ignore[attr-defined]
        wintypes.HANDLE(handle), ctypes.byref(information)
    ):
        raise ctypes.WinError(ctypes.get_last_error())
    attributes = int(information.dwFileAttributes)
    if attributes & 0x00000400:
        raise R34PathSafetyError(f"regular-file handle is a reparse point: {path}")
    if attributes & 0x00000010:
        raise R34PathSafetyError(f"regular-file handle is a directory: {path}")
    file_index = (int(information.nFileIndexHigh) << 32) | int(
        information.nFileIndexLow
    )
    return int(information.dwVolumeSerialNumber), file_index


def regular_file_stream_identity(stream: BinaryIO, path: Path) -> FileObjectIdentity:
    """Read identity from the exact creator stream handle, never from its name."""

    if os.name != "nt":
        status = os.fstat(stream.fileno())
        return int(status.st_dev), int(status.st_ino)
    kernel32 = _configured_kernel32()
    handle = int(msvcrt.get_osfhandle(stream.fileno()))
    return _regular_identity_from_handle(kernel32, handle, path)


def regular_file_object_identity(path: Path) -> FileObjectIdentity:
    """Open the named reparse object itself and return its handle identity."""

    if os.name != "nt":
        status = os.lstat(path)
        if stat.S_ISLNK(status.st_mode) or not stat.S_ISREG(status.st_mode):
            raise R34PathSafetyError(f"object is not a regular file: {path}")
        return int(status.st_dev), int(status.st_ino)
    kernel32 = _configured_kernel32()
    handle = kernel32.CreateFileW(  # type: ignore[attr-defined]
        str(path),
        0x80000000,
        0x00000001,
        None,
        3,
        0x00200000,
        None,
    )
    invalid = ctypes.c_void_p(-1).value
    if int(handle) == invalid:
        raise ctypes.WinError(ctypes.get_last_error())
    try:
        return _regular_identity_from_handle(kernel32, int(handle), path)
    finally:
        kernel32.CloseHandle(handle)  # type: ignore[attr-defined]


@contextmanager
def create_new_exclusive_binary(
    path: Path, *, buffering: int = -1
) -> Iterator[tuple[BinaryIO, FileObjectIdentity]]:
    """Atomically create a file and retain its exact deny-sharing creator handle."""

    if os.name != "nt":
        with path.open("x+b", buffering=buffering) as stream:
            yield stream, regular_file_stream_identity(stream, path)
        return
    kernel32 = _configured_kernel32()
    handle = kernel32.CreateFileW(  # type: ignore[attr-defined]
        str(path),
        0x80000000 | 0x40000000,
        0,
        None,
        1,
        0x00000080 | 0x00200000,
        None,
    )
    invalid = ctypes.c_void_p(-1).value
    if int(handle) == invalid:
        raise ctypes.WinError(ctypes.get_last_error())
    file_descriptor: int | None = None
    try:
        identity = _regular_identity_from_handle(kernel32, int(handle), path)
        file_descriptor = msvcrt.open_osfhandle(
            int(handle), os.O_BINARY | os.O_RDWR
        )
        handle = None
        with os.fdopen(file_descriptor, "w+b", buffering=buffering) as stream:
            file_descriptor = None
            yield stream, identity
    finally:
        if file_descriptor is not None:
            os.close(file_descriptor)
        if handle is not None:
            kernel32.CloseHandle(handle)  # type: ignore[attr-defined]


class WindowsDirectoryGuard:
    """Hold a directory open read-only with no write/delete sharing.

    Child files remain creatable by this process, while the directory object
    itself cannot be renamed, deleted, opened for reparse mutation, or swapped
    until the guard closes.  Exact child inventory is still the caller's job.
    """

    GENERIC_READ = 0x80000000
    FILE_SHARE_READ = 0x00000001
    OPEN_EXISTING = 3
    FILE_FLAG_BACKUP_SEMANTICS = 0x02000000
    FILE_FLAG_OPEN_REPARSE_POINT = 0x00200000
    FILE_ATTRIBUTE_DIRECTORY = 0x00000010
    FILE_ATTRIBUTE_REPARSE_POINT = 0x00000400

    def __init__(self, path: Path) -> None:
        if os.name != "nt":
            raise R34PathSafetyError("directory-object guarding requires Windows")
        self.path = path
        self.kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
        self.kernel32.CreateFileW.argtypes = (
            wintypes.LPCWSTR,
            wintypes.DWORD,
            wintypes.DWORD,
            ctypes.c_void_p,
            wintypes.DWORD,
            wintypes.DWORD,
            wintypes.HANDLE,
        )
        self.kernel32.CreateFileW.restype = wintypes.HANDLE
        self.kernel32.GetFileInformationByHandle.argtypes = (
            wintypes.HANDLE,
            ctypes.POINTER(_BY_HANDLE_FILE_INFORMATION),
        )
        self.kernel32.GetFileInformationByHandle.restype = wintypes.BOOL
        self.kernel32.CloseHandle.argtypes = (wintypes.HANDLE,)
        self.kernel32.CloseHandle.restype = wintypes.BOOL
        self.handle = self.kernel32.CreateFileW(
            str(path),
            self.GENERIC_READ,
            self.FILE_SHARE_READ,
            None,
            self.OPEN_EXISTING,
            self.FILE_FLAG_BACKUP_SEMANTICS | self.FILE_FLAG_OPEN_REPARSE_POINT,
            None,
        )
        invalid = ctypes.c_void_p(-1).value
        if int(self.handle) == invalid:
            raise ctypes.WinError(ctypes.get_last_error())
        information = _BY_HANDLE_FILE_INFORMATION()
        if not self.kernel32.GetFileInformationByHandle(
            self.handle, ctypes.byref(information)
        ):
            error = ctypes.WinError(ctypes.get_last_error())
            self.close()
            raise error
        attributes = int(information.dwFileAttributes)
        if not attributes & self.FILE_ATTRIBUTE_DIRECTORY:
            self.close()
            raise R34PathSafetyError(f"guarded object is not a directory: {path}")
        if attributes & self.FILE_ATTRIBUTE_REPARSE_POINT:
            self.close()
            raise R34PathSafetyError(f"guarded directory is a reparse point: {path}")
        self.identity = (
            int(information.dwVolumeSerialNumber),
            int(information.nFileIndexHigh),
            int(information.nFileIndexLow),
        )

    def close(self) -> None:
        if self.handle:
            self.kernel32.CloseHandle(self.handle)
            self.handle = None

    def __enter__(self) -> "WindowsDirectoryGuard":
        return self

    def __exit__(self, *_unused: object) -> None:
        self.close()


class WindowsReadLocks:
    """Keep regular files readable while denying concurrent write/delete opens."""

    GENERIC_READ = 0x80000000
    FILE_SHARE_READ = 0x00000001
    OPEN_EXISTING = 3
    FILE_FLAG_OPEN_REPARSE_POINT = 0x00200000

    def __init__(self, paths: list[Path]) -> None:
        if os.name != "nt":
            raise R34PathSafetyError("immutable file handles require Windows")
        self.paths = paths
        self.kernel32 = _configured_kernel32()
        self.handles: list[int] = []
        self.identities: dict[Path, FileObjectIdentity] = {}

    def __enter__(self) -> "WindowsReadLocks":
        invalid = ctypes.c_void_p(-1).value
        try:
            for path in self.paths:
                handle = self.kernel32.CreateFileW(
                    str(path),
                    self.GENERIC_READ,
                    self.FILE_SHARE_READ,
                    None,
                    self.OPEN_EXISTING,
                    self.FILE_FLAG_OPEN_REPARSE_POINT,
                    None,
                )
                if int(handle) == invalid:
                    raise ctypes.WinError(
                        ctypes.get_last_error(), f"cannot read-lock regular file {path}"
                    )
                handle_value = int(handle)
                # Register immediately: if any subsequent handle validation
                # fails, the common exception path must still close this handle.
                self.handles.append(handle_value)
                identity = _regular_identity_from_handle(
                    self.kernel32, handle_value, path
                )
                # Re-open the live name while the first handle denies
                # write/delete; a transient reparse or name swap must differ.
                if regular_file_object_identity(path) != identity:
                    raise R34PathSafetyError(
                        f"locked handle does not match live file name: {path}"
                    )
                self.identities[path] = identity
            for path, identity in self.identities.items():
                if regular_file_object_identity(path) != identity:
                    raise R34PathSafetyError(
                        f"file name changed while acquiring read locks: {path}"
                    )
        except BaseException:
            self.close()
            raise
        return self

    def close(self) -> None:
        while self.handles:
            self.kernel32.CloseHandle(wintypes.HANDLE(self.handles.pop()))
        self.identities.clear()

    def __exit__(self, *_unused: object) -> None:
        self.close()


def require_absolute_s_no_parent(path: Path, label: str) -> Path:
    parsed = PureWindowsPath(str(path))
    if not parsed.is_absolute() or parsed.drive.upper() != "S:":
        raise R34PathSafetyError(f"{label} must be an absolute S: path: {path}")
    if ".." in parsed.parts:
        raise R34PathSafetyError(f"{label} must not contain '..': {path}")
    return path


def reject_reparse_between(path: Path, root: Path, label: str) -> None:
    """Reject every existing symlink/junction/reparse component through root.

    This lower-level helper is root-agnostic so local tests can inject a
    reparse mutant without touching S:.  Missing suffixes are allowed for a
    not-yet-created atomic target, but every existing ancestor is checked.
    """

    absolute_path = path.absolute()
    absolute_root = root.absolute()
    try:
        absolute_path.relative_to(absolute_root)
    except ValueError as error:
        raise R34PathSafetyError(f"{label} is outside guarded root {root}") from error
    current = absolute_path
    while True:
        try:
            status = os.lstat(current)
        except FileNotFoundError:
            pass
        else:
            attributes = getattr(status, "st_file_attributes", 0)
            if attributes & 0x00000400 or stat.S_ISLNK(status.st_mode):
                raise R34PathSafetyError(f"{label} crosses reparse point {current}")
        if current == absolute_root:
            break
        parent = current.parent
        if parent == current:
            raise R34PathSafetyError(f"{label} did not reach guarded root {root}")
        current = parent


def reject_absolute_s_reparse(path: Path, label: str) -> Path:
    path = require_absolute_s_no_parent(path, label)
    parsed = PureWindowsPath(str(path))
    reject_reparse_between(path, Path(parsed.anchor), label)
    return path


def require_existing_directory(path: Path, label: str) -> Path:
    reject_absolute_s_reparse(path, label)
    if not path.is_dir():
        raise FileNotFoundError(f"{label} does not exist or is not a directory: {path}")
    # Re-check the final component after the type query to narrow substitution.
    reject_absolute_s_reparse(path, label)
    return path


def require_existing_regular_file(path: Path, label: str) -> Path:
    reject_absolute_s_reparse(path, label)
    if not path.is_file():
        raise FileNotFoundError(f"{label} does not exist or is not a regular file: {path}")
    reject_absolute_s_reparse(path, label)
    return path
