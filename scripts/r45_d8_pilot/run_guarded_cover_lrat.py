#!/usr/bin/env python3
"""Resumable CaDiCaL/LRAT runner for the frozen degree-eight guarded cover.

Large CNFs and proofs are written only below the mandatory ``--output``
directory, which must be outside the repository.  For cover cube ``i``, the
input is byte-deterministically reconstructed as ``Cover.Cube.leafCNF``:
the cube's unit clauses first, followed by all 55,926 master clauses.

The runner is deliberately separate from certificate verification in Lean.
It records hashes and CaDiCaL's UNSAT status, while the resulting files still
need replay through ``LRATCatcher.Cover`` before they become proof artifacts.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import time
import uuid
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence


HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parents[1]
DEFAULT_ARTIFACTS = HERE / "guarded_master"
MASTER_NAME = "guarded_master.cnf"
COVER_NAME = "cover.icnf"
MANIFEST_NAME = "cube_manifest.json"
METADATA_NAME = "metadata.json"
NEGATED_COVER_NAME = "negated_cover.cnf"
PROOF_BUNDLE_MANIFEST_NAME = "proof_bundle_manifest.json"

EXPECTED_VARIABLES = 282
EXPECTED_MASTER_CLAUSES = 55_926
EXPECTED_CUBES = 59
SOLVER_FLAGS = ("--lrat", "--no-binary", "--unsat", "--walk=false")

Clause = tuple[int, ...]


class RunnerError(RuntimeError):
    pass


@dataclass(frozen=True)
class SourceBundle:
    artifacts: Path
    master_path: Path
    master_body: bytes
    master_sha256: str
    master_variables: int
    master_clauses: int
    cover_path: Path
    cover_sha256: str
    cubes: tuple[Clause, ...]
    cover_rows: tuple[dict, ...]
    manifest_sha256: str
    metadata_sha256: str
    negated_cover_path: Path
    negated_cover_sha256: str

    def identity(self) -> dict[str, str]:
        return {
            "guarded_master_cnf_sha256": self.master_sha256,
            "cover_icnf_sha256": self.cover_sha256,
            "cube_manifest_sha256": self.manifest_sha256,
            "metadata_sha256": self.metadata_sha256,
            "negated_cover_cnf_sha256": self.negated_cover_sha256,
        }


@dataclass(frozen=True)
class Job:
    kind: str
    stem: str
    index_one_based: int | None = None
    cube: Clause = ()


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def json_bytes(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def atomic_write_bytes(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp.{os.getpid()}.{uuid.uuid4().hex}")
    try:
        with temporary.open("xb") as stream:
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def atomic_write_json(path: Path, value: object) -> None:
    atomic_write_bytes(path, json_bytes(value))


def parse_icnf_bytes(data: bytes) -> tuple[Clause, ...]:
    cubes: list[Clause] = []
    for line_number, raw_line in enumerate(data.decode("ascii").splitlines(), 1):
        line = raw_line.strip()
        if not line or line.startswith("c") or line.startswith("p"):
            continue
        tokens = line.split()
        if not tokens or tokens[0] != "a":
            raise RunnerError(f"invalid iCNF line {line_number}: {line!r}")
        try:
            values = [int(token) for token in tokens[1:]]
        except ValueError as exc:
            raise RunnerError(f"non-integer iCNF token on line {line_number}") from exc
        if not values or values[-1] != 0 or values.count(0) != 1:
            raise RunnerError(f"invalid iCNF terminator on line {line_number}")
        cubes.append(tuple(values[:-1]))
    return tuple(cubes)


def parse_dimacs_bytes(data: bytes) -> tuple[int, tuple[Clause, ...], bytes]:
    lines = data.splitlines(keepends=True)
    if not lines:
        raise RunnerError("empty DIMACS input")
    header_tokens = lines[0].decode("ascii").strip().split()
    if len(header_tokens) != 4 or header_tokens[:2] != ["p", "cnf"]:
        raise RunnerError("DIMACS must begin with a strict 'p cnf V C' header")
    try:
        variables = int(header_tokens[2])
        declared_clauses = int(header_tokens[3])
    except ValueError as exc:
        raise RunnerError("non-integer DIMACS header") from exc
    clauses: list[Clause] = []
    for line_number, raw_line in enumerate(lines[1:], 2):
        line = raw_line.decode("ascii").strip()
        if not line or line.startswith("c"):
            continue
        try:
            values = [int(token) for token in line.split()]
        except ValueError as exc:
            raise RunnerError(f"non-integer DIMACS token on line {line_number}") from exc
        if not values or values[-1] != 0 or values.count(0) != 1:
            raise RunnerError(f"invalid DIMACS clause line {line_number}")
        clause = tuple(values[:-1])
        if not clause:
            raise RunnerError(f"unexpected empty DIMACS clause on line {line_number}")
        if any(abs(literal) > variables for literal in clause):
            raise RunnerError(f"out-of-range DIMACS literal on line {line_number}")
        clauses.append(clause)
    if len(clauses) != declared_clauses:
        raise RunnerError(
            f"DIMACS declares {declared_clauses} clauses but contains {len(clauses)}"
        )
    return variables, tuple(clauses), b"".join(lines[1:])


def load_sources(artifacts: Path = DEFAULT_ARTIFACTS) -> SourceBundle:
    artifacts = artifacts.resolve()
    paths = {
        "master": artifacts / MASTER_NAME,
        "cover": artifacts / COVER_NAME,
        "manifest": artifacts / MANIFEST_NAME,
        "metadata": artifacts / METADATA_NAME,
        "negated": artifacts / NEGATED_COVER_NAME,
    }
    for path in paths.values():
        if not path.is_file():
            raise RunnerError(f"missing frozen artifact: {path}")

    metadata_data = paths["metadata"].read_bytes()
    manifest_data = paths["manifest"].read_bytes()
    metadata = json.loads(metadata_data)
    manifest = json.loads(manifest_data)
    master_data = paths["master"].read_bytes()
    cover_data = paths["cover"].read_bytes()
    negated_data = paths["negated"].read_bytes()

    master_hash = sha256_bytes(master_data)
    cover_hash = sha256_bytes(cover_data)
    manifest_hash = sha256_bytes(manifest_data)
    metadata_hash = sha256_bytes(metadata_data)
    negated_hash = sha256_bytes(negated_data)
    expected = {
        "master": metadata["cnf"]["sha256"],
        "cover": metadata["cube_manifest"]["cover_icnf_sha256"],
        "manifest": metadata["cube_manifest"]["sha256"],
        "negated": metadata["negated_cover_cnf"]["sha256"],
    }
    actual = {
        "master": master_hash,
        "cover": cover_hash,
        "manifest": manifest_hash,
        "negated": negated_hash,
    }
    for name in expected:
        if actual[name] != expected[name]:
            raise RunnerError(
                f"frozen {name} hash mismatch: {actual[name]} != {expected[name]}"
            )

    variables, master_clauses, master_body = parse_dimacs_bytes(master_data)
    if (variables, len(master_clauses)) != (
        EXPECTED_VARIABLES,
        EXPECTED_MASTER_CLAUSES,
    ):
        raise RunnerError("guarded master dimensions changed")
    cubes = parse_icnf_bytes(cover_data)
    if len(cubes) != EXPECTED_CUBES:
        raise RunnerError(f"cover has {len(cubes)} cubes instead of {EXPECTED_CUBES}")
    rows = tuple(manifest["cubes"])
    if len(rows) != EXPECTED_CUBES:
        raise RunnerError("cube manifest does not contain 59 ordered rows")
    for index, (cube, row) in enumerate(zip(cubes, rows, strict=True), 1):
        if row["cover_index_one_based"] != index:
            raise RunnerError(f"manifest proof-order mismatch at cube {index}")
        if tuple(row["cube"]) != cube:
            raise RunnerError(f"manifest/iCNF cube mismatch at index {index}")

    negated_variables, negated_clauses, _ = parse_dimacs_bytes(negated_data)
    expected_negated = tuple(tuple(-literal for literal in cube) for cube in cubes)
    if negated_variables != EXPECTED_VARIABLES or negated_clauses != expected_negated:
        raise RunnerError("negated_cover.cnf is not Cover.negCubesCNF in iCNF order")

    return SourceBundle(
        artifacts=artifacts,
        master_path=paths["master"],
        master_body=master_body,
        master_sha256=master_hash,
        master_variables=variables,
        master_clauses=len(master_clauses),
        cover_path=paths["cover"],
        cover_sha256=cover_hash,
        cubes=cubes,
        cover_rows=rows,
        manifest_sha256=manifest_hash,
        metadata_sha256=metadata_hash,
        negated_cover_path=paths["negated"],
        negated_cover_sha256=negated_hash,
    )


def load_proof_bundle_manifest(bundle: SourceBundle) -> dict:
    path = bundle.artifacts / PROOF_BUNDLE_MANIFEST_NAME
    if not path.is_file():
        raise RunnerError(f"missing proof-bundle manifest: {path}")
    manifest = json.loads(path.read_bytes())
    if manifest.get("schema_version") != 1:
        raise RunnerError("unsupported proof-bundle manifest schema")
    if manifest.get("source_artifacts") != bundle.identity():
        raise RunnerError("proof-bundle source identity does not match frozen inputs")

    files = manifest.get("files")
    if not isinstance(files, list):
        raise RunnerError("proof-bundle manifest has no ordered file list")
    expected_names = [
        *(f"leaf_{index}.lrat" for index in range(1, EXPECTED_CUBES + 1)),
        "cover.lrat",
    ]
    names = [entry.get("name") for entry in files]
    if names != expected_names:
        raise RunnerError("proof-bundle files are not leaf_1..leaf_59 then cover.lrat")
    for entry in files:
        name = entry.get("name")
        size = entry.get("bytes")
        digest = entry.get("sha256")
        if not isinstance(name, str) or Path(name).name != name:
            raise RunnerError(f"non-local proof-bundle filename: {name!r}")
        if not isinstance(size, int) or size <= 0:
            raise RunnerError(f"invalid proof-bundle size for {name}")
        if (
            not isinstance(digest, str)
            or len(digest) != 64
            or digest != digest.upper()
            or any(character not in "0123456789ABCDEF" for character in digest)
        ):
            raise RunnerError(f"invalid proof-bundle SHA-256 for {name}")

    bundle_info = manifest.get("bundle", {})
    total = sum(entry["bytes"] for entry in files)
    if bundle_info.get("lrat_files") != len(files):
        raise RunnerError("proof-bundle file count mismatch")
    if bundle_info.get("leaf_lrat_files") != EXPECTED_CUBES:
        raise RunnerError("proof-bundle leaf count mismatch")
    if bundle_info.get("cover_lrat_files") != 1:
        raise RunnerError("proof-bundle cover count mismatch")
    if bundle_info.get("total_lrat_bytes") != total:
        raise RunnerError("proof-bundle byte total mismatch")
    return manifest


def verify_proof_bundle(bundle: SourceBundle, output: Path) -> dict:
    manifest = load_proof_bundle_manifest(bundle)
    output = ensure_external_output(output)
    expected_names = {entry["name"] for entry in manifest["files"]}
    present_names = {path.name for path in output.glob("*.lrat") if path.is_file()}
    if present_names != expected_names:
        missing = sorted(expected_names - present_names)
        unexpected = sorted(present_names - expected_names)
        raise RunnerError(
            f"proof-bundle filenames differ; missing={missing}, unexpected={unexpected}"
        )
    for entry in manifest["files"]:
        path = output / entry["name"]
        if path.stat().st_size != entry["bytes"]:
            raise RunnerError(f"proof-bundle size mismatch: {path}")
        if sha256_file(path) != entry["sha256"]:
            raise RunnerError(f"proof-bundle hash mismatch: {path}")
    return {
        "schema_version": 1,
        "status": "VERIFIED_COMPLETE_PROOF_BUNDLE",
        "output": str(output),
        "source_artifacts": bundle.identity(),
        "lrat_files": len(manifest["files"]),
        "total_lrat_bytes": manifest["bundle"]["total_lrat_bytes"],
    }


def leaf_cnf_bytes(bundle: SourceBundle, index_one_based: int) -> bytes:
    if not 1 <= index_one_based <= len(bundle.cubes):
        raise RunnerError(f"leaf index out of range: {index_one_based}")
    cube = bundle.cubes[index_one_based - 1]
    header = (
        f"p cnf {bundle.master_variables} "
        f"{bundle.master_clauses + len(cube)}\n"
    ).encode("ascii")
    units = b"".join(f"{literal} 0\n".encode("ascii") for literal in cube)
    return header + units + bundle.master_body


def solver_command(
    solver: Path,
    input_cnf: Path,
    output_lrat: Path,
    conflicts: int | None = None,
) -> list[str]:
    command = [str(solver), *SOLVER_FLAGS]
    if conflicts is not None:
        command.extend(["-c", str(conflicts)])
    command.extend([str(input_cnf), str(output_lrat)])
    return command


def parse_indices(specifications: Sequence[str] | None) -> list[int]:
    if not specifications:
        return list(range(1, EXPECTED_CUBES + 1))
    selected: set[int] = set()
    for specification in specifications:
        for item in specification.split(","):
            item = item.strip()
            if not item:
                continue
            if "-" in item:
                first_text, last_text = item.split("-", 1)
                first, last = int(first_text), int(last_text)
                if first > last:
                    raise RunnerError(f"descending leaf range: {item}")
                selected.update(range(first, last + 1))
            else:
                selected.add(int(item))
    if not selected or min(selected) < 1 or max(selected) > EXPECTED_CUBES:
        raise RunnerError("leaf filters must select indices in 1,...,59")
    return sorted(selected)


def ensure_external_output(output: Path) -> Path:
    resolved = output.resolve()
    try:
        resolved.relative_to(REPO_ROOT.resolve())
    except ValueError:
        return resolved
    raise RunnerError(
        f"refusing large runner output inside repository {REPO_ROOT}; "
        "choose an external --output (for example on S:)"
    )


def job_paths(output: Path, job: Job) -> dict[str, Path]:
    return {
        "cnf": output / f"{job.stem}.cnf",
        "proof": output / f"{job.stem}.lrat",
        "log": output / f"{job.stem}.log",
        "metadata": output / f"{job.stem}.json",
    }


def expected_input(bundle: SourceBundle, job: Job) -> tuple[bytes | None, Path | None, str, int]:
    if job.kind == "leaf":
        data = leaf_cnf_bytes(bundle, job.index_one_based or 0)
        return data, None, sha256_bytes(data), bundle.master_clauses + len(job.cube)
    if job.kind == "cover":
        return (
            None,
            bundle.negated_cover_path,
            bundle.negated_cover_sha256,
            EXPECTED_CUBES,
        )
    raise RunnerError(f"unknown job kind {job.kind}")


def build_jobs(bundle: SourceBundle, indices: Sequence[int], include_cover: bool) -> list[Job]:
    jobs = [
        Job("leaf", f"leaf_{index}", index, bundle.cubes[index - 1])
        for index in indices
    ]
    if include_cover:
        jobs.append(Job("cover", "cover"))
    return jobs


def build_dry_run_plan(
    bundle: SourceBundle,
    solver: Path,
    output: Path,
    indices: Sequence[int],
    include_cover: bool,
    conflicts: int | None,
) -> dict:
    planned: list[dict] = []
    for job in build_jobs(bundle, indices, include_cover):
        paths = job_paths(output, job)
        _data, source_path, input_hash, clause_count = expected_input(bundle, job)
        input_path = paths["cnf"] if job.kind == "leaf" else source_path
        planned.append(
            {
                "kind": job.kind,
                "index_one_based": job.index_one_based,
                "stem": job.stem,
                "cube": list(job.cube),
                "input_cnf_sha256": input_hash,
                "input_clause_count": clause_count,
                "command": solver_command(
                    solver, input_path or paths["cnf"], paths["proof"], conflicts
                ),
            }
        )
    return {
        "schema_version": 1,
        "status": "DRY_RUN_NO_SOLVER_INVOKED",
        "source_artifacts": bundle.identity(),
        "jobs": planned,
    }


def validate_completed_job(bundle: SourceBundle, output: Path, job: Job) -> dict | None:
    paths = job_paths(output, job)
    if not paths["metadata"].is_file():
        if paths["proof"].exists() or paths["log"].exists():
            raise RunnerError(
                f"orphan final artifact for {job.stem}; move it aside before resume"
            )
        return None
    record = json.loads(paths["metadata"].read_text(encoding="utf-8"))
    if record.get("status") != "UNSAT_WITH_LRAT":
        return None
    _data, _source, expected_hash, expected_clauses = expected_input(bundle, job)
    checks = {
        "kind": job.kind,
        "input_cnf_sha256": expected_hash,
        "input_clause_count": expected_clauses,
        "source_artifacts": bundle.identity(),
    }
    if job.kind == "leaf":
        checks["index_one_based"] = job.index_one_based
        checks["cube"] = list(job.cube)
    for key, expected_value in checks.items():
        if record.get(key) != expected_value:
            raise RunnerError(f"resume metadata mismatch for {job.stem}: {key}")
    for key, path_key in (("lrat", "proof"), ("log", "log")):
        path = paths[path_key]
        if not path.is_file() or path.stat().st_size == 0:
            raise RunnerError(f"completed {job.stem} is missing {path.name}")
        if record[key]["sha256"] != sha256_file(path):
            raise RunnerError(f"resume hash mismatch for {path}")
        if record[key]["bytes"] != path.stat().st_size:
            raise RunnerError(f"resume size mismatch for {path}")
    log_data = paths["log"].read_bytes()
    if b"s UNSATISFIABLE" not in log_data:
        raise RunnerError(f"completed {job.stem} log lacks UNSAT status")
    if paths["cnf"].exists() and sha256_file(paths["cnf"]) != expected_hash:
        raise RunnerError(f"kept CNF hash mismatch for {job.stem}")
    return record


def remove_stale_partials(output: Path, stem: str) -> None:
    for path in output.glob(f"{stem}.lrat.partial.*"):
        path.unlink()


def execute_job(
    bundle: SourceBundle,
    solver: Path,
    solver_sha256: str,
    output: Path,
    job: Job,
    conflicts: int | None,
    timeout: float | None,
    keep_cnfs: bool,
) -> dict:
    completed = validate_completed_job(bundle, output, job)
    if completed is not None:
        return {**completed, "resume": "SKIPPED_VERIFIED_COMPLETE"}

    paths = job_paths(output, job)
    remove_stale_partials(output, job.stem)
    input_data, source_path, input_hash, clause_count = expected_input(bundle, job)
    if job.kind == "leaf":
        atomic_write_bytes(paths["cnf"], input_data or b"")
        input_path = paths["cnf"]
    else:
        input_path = source_path or bundle.negated_cover_path

    proof_partial = output / f"{job.stem}.lrat.partial.{uuid.uuid4().hex}"
    command = solver_command(solver, input_path, proof_partial, conflicts)
    started = time.perf_counter()
    timed_out = False
    returncode: int | None = None
    log_data = b""
    error_text: str | None = None
    try:
        result = subprocess.run(
            command,
            cwd=output,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
        )
        returncode = result.returncode
        log_data = result.stdout
    except subprocess.TimeoutExpired as exc:
        timed_out = True
        partial = exc.stdout or b""
        log_data = partial.encode("utf-8", "replace") if isinstance(partial, str) else partial
        error_text = f"timeout after {timeout} seconds"
    except Exception as exc:  # recorded atomically for resumable diagnostics
        error_text = f"{type(exc).__name__}: {exc}"
    elapsed = time.perf_counter() - started
    atomic_write_bytes(paths["log"], log_data)

    unsat = returncode == 20 and b"s UNSATISFIABLE" in log_data
    proof_ok = proof_partial.is_file() and proof_partial.stat().st_size > 0
    status = "UNSAT_WITH_LRAT" if unsat and proof_ok else (
        "TIMEOUT" if timed_out else "FAILED"
    )
    if status == "UNSAT_WITH_LRAT":
        os.replace(proof_partial, paths["proof"])
    elif proof_partial.exists():
        proof_partial.unlink()

    record = {
        "schema_version": 1,
        "status": status,
        "kind": job.kind,
        "index_one_based": job.index_one_based,
        "cube": list(job.cube),
        "input_cnf_sha256": input_hash,
        "input_clause_count": clause_count,
        "source_artifacts": bundle.identity(),
        "solver": {
            "path": str(solver),
            "sha256": solver_sha256,
            "flags": list(SOLVER_FLAGS),
        },
        "command": command,
        "returncode": returncode,
        "timeout_seconds": timeout,
        "conflict_limit": conflicts,
        "elapsed_seconds": elapsed,
        "error": error_text,
        "log": {
            "name": paths["log"].name,
            "bytes": paths["log"].stat().st_size,
            "sha256": sha256_file(paths["log"]),
        },
    }
    if status == "UNSAT_WITH_LRAT":
        record["lrat"] = {
            "name": paths["proof"].name,
            "bytes": paths["proof"].stat().st_size,
            "sha256": sha256_file(paths["proof"]),
        }
    else:
        record["lrat"] = {"name": paths["proof"].name, "bytes": 0, "sha256": None}

    if job.kind == "leaf" and paths["cnf"].exists() and not keep_cnfs:
        paths["cnf"].unlink()
    record["cnf_retained"] = paths["cnf"].is_file() if job.kind == "leaf" else True
    atomic_write_json(paths["metadata"], record)
    return record


def run(args: argparse.Namespace) -> int:
    bundle = load_sources(args.artifacts)
    output = ensure_external_output(args.output)
    if args.verify_bundle:
        print(json.dumps(verify_proof_bundle(bundle, output), indent=2, sort_keys=True))
        return 0
    if args.solver is None:
        raise RunnerError("--solver is required unless --verify-bundle is used")
    solver = args.solver.resolve()
    if not solver.is_file():
        raise RunnerError(f"solver not found: {solver}")
    if args.jobs < 1:
        raise RunnerError("--jobs must be positive")
    if args.conflicts is not None and args.conflicts < 1:
        raise RunnerError("--conflicts must be positive")
    if args.timeout is not None and args.timeout <= 0:
        raise RunnerError("--timeout must be positive")
    if args.cover_only and args.skip_cover:
        raise RunnerError("--cover-only and --skip-cover are incompatible")

    indices = [] if args.cover_only else parse_indices(args.only)
    include_cover = not args.skip_cover
    output.mkdir(parents=True, exist_ok=True)
    if args.dry_run:
        plan = build_dry_run_plan(
            bundle, solver, output, indices, include_cover, args.conflicts
        )
        atomic_write_json(output / "dry_run_plan.json", plan)
        print(json.dumps(plan, indent=2, sort_keys=True))
        return 0

    solver_hash = sha256_file(solver)
    leaf_jobs = build_jobs(bundle, indices, include_cover=False)
    records: list[dict] = []
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = {
            pool.submit(
                execute_job,
                bundle,
                solver,
                solver_hash,
                output,
                job,
                args.conflicts,
                args.timeout,
                args.keep_cnfs,
            ): job
            for job in leaf_jobs
        }
        for future in as_completed(futures):
            job = futures[future]
            try:
                record = future.result()
            except Exception as exc:
                record = {
                    "kind": job.kind,
                    "index_one_based": job.index_one_based,
                    "status": "RUNNER_ERROR",
                    "error": f"{type(exc).__name__}: {exc}",
                }
            records.append(record)
            print(f"{job.stem}: {record['status']}", flush=True)

    if include_cover:
        cover_job = Job("cover", "cover")
        try:
            cover_record = execute_job(
                bundle,
                solver,
                solver_hash,
                output,
                cover_job,
                args.conflicts,
                args.timeout,
                keep_cnfs=True,
            )
        except Exception as exc:
            cover_record = {
                "kind": "cover",
                "index_one_based": None,
                "status": "RUNNER_ERROR",
                "error": f"{type(exc).__name__}: {exc}",
            }
        records.append(cover_record)
        print(f"cover: {cover_record['status']}", flush=True)

    records.sort(key=lambda record: (
        record.get("kind") == "cover",
        record.get("index_one_based") or 0,
    ))
    all_selected_complete = all(
        record["status"] == "UNSAT_WITH_LRAT"
        or record.get("resume") == "SKIPPED_VERIFIED_COMPLETE"
        for record in records
    )
    full_cover_requested = (
        indices == list(range(1, EXPECTED_CUBES + 1)) and include_cover
    )
    if not all_selected_complete:
        run_status = "INCOMPLETE"
    elif full_cover_requested:
        run_status = "COMPLETE_FULL_COVER_RUN"
    else:
        run_status = "COMPLETE_SELECTED_JOBS"
    summary = {
        "schema_version": 1,
        "status": run_status,
        "source_artifacts": bundle.identity(),
        "solver": {"path": str(solver), "sha256": solver_hash},
        "output": str(output),
        "jobs_requested": args.jobs,
        "selected_leaf_indices": indices,
        "cover_requested": include_cover,
        "keep_cnfs": args.keep_cnfs,
        "records": records,
    }
    atomic_write_json(output / "run_metadata.json", summary)
    print(json.dumps({key: value for key, value in summary.items() if key != "records"},
                     indent=2, sort_keys=True))
    return 0 if all_selected_complete else 1


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--solver", type=Path)
    result.add_argument("--output", required=True, type=Path)
    result.add_argument("--artifacts", type=Path, default=DEFAULT_ARTIFACTS)
    result.add_argument("--jobs", type=int, default=1)
    result.add_argument(
        "--only", action="append",
        help="leaf indices/ranges, for example --only 1,2,55-59",
    )
    result.add_argument("--conflicts", type=int)
    result.add_argument("--timeout", type=float)
    result.add_argument("--keep-cnfs", action="store_true")
    result.add_argument("--skip-cover", action="store_true")
    result.add_argument("--cover-only", action="store_true")
    result.add_argument("--dry-run", action="store_true")
    result.add_argument(
        "--verify-bundle", action="store_true",
        help="hash-check the exact 60-file LRAT bundle without invoking a solver",
    )
    return result


def main() -> int:
    try:
        return run(parser().parse_args())
    except Exception as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
