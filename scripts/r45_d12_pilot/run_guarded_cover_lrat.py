#!/usr/bin/env python3
"""SSD-only LRAT runner for the degree-twelve guarded master.

This adapter deliberately reuses the already tested degree-eight runner.  It
only changes the frozen source validation, the expected dimensions, and the
disk policy.  Every CLI run requires both the generated d12 artifacts and the
runner output to be given explicitly; all output must be below an absolute
``S:`` path.

The runner records CaDiCaL's UNSAT status and LRAT hashes.  Those files are not
Lean theorems until they have also been replayed through LRATCatcher.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path, PureWindowsPath
from typing import Sequence


HERE = Path(__file__).resolve().parent
REPOSITORY = HERE.parents[1]
BASE_RUNNER_PATH = REPOSITORY / "scripts" / "r45_d8_pilot" / "run_guarded_cover_lrat.py"

EXPECTED_VARIABLES = 280
EXPECTED_MASTER_CLAUSES = 54_638
EXPECTED_CUBES = 13


def load_base_runner():
    specification = importlib.util.spec_from_file_location(
        "r45_d12_reused_guarded_runner", BASE_RUNNER_PATH
    )
    if specification is None or specification.loader is None:
        raise RuntimeError(f"cannot import {BASE_RUNNER_PATH}")
    module = importlib.util.module_from_spec(specification)
    sys.modules[specification.name] = module
    specification.loader.exec_module(module)
    return module


base = load_base_runner()
RunnerError = base.RunnerError
SourceBundle = base.SourceBundle


def require_explicit_ssd_path(path: Path) -> Path:
    """Return an absolute S: path and reject every other spelling."""
    windows_path = PureWindowsPath(str(path))
    if windows_path.drive.upper() != "S:" or not windows_path.is_absolute():
        raise RunnerError(
            f"path must be explicit and rooted on S:, received {path}"
        )
    return path.resolve()


def _expected_hashes(metadata: dict) -> dict[str, str]:
    return {
        "master": metadata["cnf"]["sha256"],
        "cover": metadata["hashes"]["cover_icnf_sha256"],
        "manifest": metadata["hashes"]["cube_manifest_sha256"],
        "negated": metadata["hashes"]["negated_cover_cnf_sha256"],
    }


def load_sources(artifacts: Path) -> SourceBundle:
    """Load and cross-check the six deterministic d12 formula artifacts."""
    artifacts = artifacts.resolve()
    paths = {
        "master": artifacts / base.MASTER_NAME,
        "cover": artifacts / base.COVER_NAME,
        "manifest": artifacts / base.MANIFEST_NAME,
        "metadata": artifacts / base.METADATA_NAME,
        "negated": artifacts / base.NEGATED_COVER_NAME,
    }
    for path in paths.values():
        if not path.is_file():
            raise RunnerError(f"missing generated d12 artifact: {path}")

    metadata_data = paths["metadata"].read_bytes()
    manifest_data = paths["manifest"].read_bytes()
    metadata = json.loads(metadata_data)
    manifest = json.loads(manifest_data)
    if metadata.get("status") != "GENERATED_NOT_SOLVED_OR_LRAT_CERTIFIED":
        raise RunnerError("unexpected d12 formula status")

    master_data = paths["master"].read_bytes()
    cover_data = paths["cover"].read_bytes()
    negated_data = paths["negated"].read_bytes()
    actual = {
        "master": base.sha256_bytes(master_data),
        "cover": base.sha256_bytes(cover_data),
        "manifest": base.sha256_bytes(manifest_data),
        "negated": base.sha256_bytes(negated_data),
    }
    expected = _expected_hashes(metadata)
    for name, expected_hash in expected.items():
        if actual[name] != expected_hash:
            raise RunnerError(
                f"generated d12 {name} hash mismatch: "
                f"{actual[name]} != {expected_hash}"
            )

    variables, master_clauses, master_body = base.parse_dimacs_bytes(master_data)
    if (variables, len(master_clauses)) != (
        EXPECTED_VARIABLES,
        EXPECTED_MASTER_CLAUSES,
    ):
        raise RunnerError("d12 guarded-master dimensions changed")

    cubes = base.parse_icnf_bytes(cover_data)
    rows = tuple(manifest.get("cubes", ()))
    if len(cubes) != EXPECTED_CUBES or len(rows) != EXPECTED_CUBES:
        raise RunnerError("d12 cover or manifest does not contain exactly 13 rows")
    for index, (cube, row) in enumerate(zip(cubes, rows, strict=True), 1):
        if row.get("cover_index_one_based") != index:
            raise RunnerError(f"d12 manifest proof-order mismatch at cube {index}")
        if tuple(row.get("cube", ())) != cube:
            raise RunnerError(f"d12 manifest/iCNF cube mismatch at index {index}")

    negated_variables, negated_clauses, _ = base.parse_dimacs_bytes(negated_data)
    expected_negated = tuple(tuple(-literal for literal in cube) for cube in cubes)
    if negated_variables != EXPECTED_VARIABLES or negated_clauses != expected_negated:
        raise RunnerError("d12 negated_cover.cnf is not Cover.negCubesCNF")

    return SourceBundle(
        artifacts=artifacts,
        master_path=paths["master"],
        master_body=master_body,
        master_sha256=actual["master"],
        master_variables=variables,
        master_clauses=len(master_clauses),
        cover_path=paths["cover"],
        cover_sha256=actual["cover"],
        cubes=cubes,
        cover_rows=rows,
        manifest_sha256=actual["manifest"],
        metadata_sha256=base.sha256_bytes(metadata_data),
        negated_cover_path=paths["negated"],
        negated_cover_sha256=actual["negated"],
    )


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
        raise RunnerError("leaf filters must select indices in 1,...,13")
    return sorted(selected)


def configure_base_runner() -> None:
    """Install the d12 dimensions and validators in the reused runner."""
    base.EXPECTED_VARIABLES = EXPECTED_VARIABLES
    base.EXPECTED_MASTER_CLAUSES = EXPECTED_MASTER_CLAUSES
    base.EXPECTED_CUBES = EXPECTED_CUBES
    base.load_sources = load_sources
    base.ensure_external_output = require_explicit_ssd_path
    base.parse_indices = parse_indices


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--solver", type=Path)
    result.add_argument("--output", required=True, type=Path)
    result.add_argument("--artifacts", required=True, type=Path)
    result.add_argument("--jobs", type=int, default=1)
    result.add_argument("--only", action="append")
    result.add_argument("--conflicts", type=int)
    result.add_argument("--timeout", type=float)
    result.add_argument("--keep-cnfs", action="store_true")
    result.add_argument("--skip-cover", action="store_true")
    result.add_argument("--cover-only", action="store_true")
    result.add_argument("--dry-run", action="store_true")
    result.add_argument("--verify-bundle", action="store_true")
    return result


def run(args: argparse.Namespace) -> int:
    configure_base_runner()
    args.output = require_explicit_ssd_path(args.output)
    return base.run(args)


def main() -> int:
    try:
        return run(parser().parse_args())
    except Exception as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
