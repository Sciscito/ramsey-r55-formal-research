#!/usr/bin/env python3
"""Validate and consolidate the 13 external Lean/LRAT certificates."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from . import certify_two_center_batch as certify
from . import generate_two_center_branches as two
from . import generate_universal as universal
from .run_solver_pilot import sha256


CASE_DIRECTORIES = {
    (0, 2): "cert_case_p0_q2_v1",
    (0, 3): "cert_case_p0_q3_v1",
    (1, 1): "cert_case_p1_q1_v1",
    (1, 2): "cert_case_p1_q2_v1",
    (1, 3): "cert_case_p1_q3_v1",
    (2, 0): "cert_case_p2_q0_canonical_v2",
    (2, 1): "cert_case_p2_q1_v1",
    (2, 2): "cert_case_p2_q2_v1",
    (2, 3): "cert_case_p2_q3_v1",
    (3, 0): "cert_case_p3_q0_v1",
    (3, 1): "cert_case_p3_q1_v1",
    (3, 2): "cert_case_p3_q2_v1",
    (3, 3): "cert_case_p3_q3_v1",
}
SOLVER_SHA256 = "AE6156A9C3BB46D8AC5E0A3892A5F11999EF6FD5F346304FD53DB9160FD5743B"
LAKE_SHA256 = "B01D614F13CFD9851110841DE640DBF82A0F73936C55F47095BF7DAA449931AC"
SOURCE_MANIFEST_SHA256 = "2D62D59D82643B43E218A58CCB762DAF02B6696F5B446D7AC16394B424B55B9A"


def relative_artifact_path(path: Path, artifact_root: Path) -> str:
    try:
        relative = path.relative_to(artifact_root)
    except ValueError as error:
        raise ValueError(f"artifact escapes --output: {path}") from error
    if relative.is_absolute() or ".." in relative.parts:
        raise ValueError(f"invalid artifact path: {path}")
    return relative.as_posix()


def checked_file(
    path: Path,
    metadata: dict[str, object],
    artifact_root: Path,
) -> dict[str, object]:
    if not path.is_file():
        raise FileNotFoundError(path)
    actual = {"bytes": path.stat().st_size, "sha256": sha256(path)}
    if actual["bytes"] != metadata["bytes"] or actual["sha256"] != metadata["sha256"]:
        raise ValueError(f"artifact identity mismatch: {path}")
    return {
        **actual,
        "artifact_path": relative_artifact_path(path, artifact_root),
    }


def load_case(directory: Path, case: tuple[int, int]) -> dict[str, object]:
    p, q = case
    artifact_root = directory.parent
    batch = directory / CASE_DIRECTORIES[case]
    case_dir = batch / f"p{p}_q{q}"
    certificate_path = case_dir / "certificate.json"
    batch_path = batch / "batch_manifest.json"
    certificate = json.loads(certificate_path.read_text(encoding="utf-8"))
    batch_manifest = json.loads(batch_path.read_text(encoding="utf-8"))
    if certificate["status"] != "LEAN_LRAT_REPLAY_SUCCEEDED":
        raise ValueError(f"uncertified case: {case}")
    if batch_manifest["status"] != "ALL_SELECTED_CASES_LEAN_LRAT_CERTIFIED":
        raise ValueError(f"incomplete one-case batch: {case}")
    if tuple(batch_manifest["case_order"][0]) != case:
        raise ValueError(f"one-case batch identity mismatch: {case}")

    expected_clauses, expected_bytes, expected_hash = two.EXPECTED_CASE_RESULTS[case]
    formula = certificate["formula"]
    observed_formula = (formula["clauses"], formula["bytes"], formula["sha256"])
    if observed_formula != (expected_clauses, expected_bytes, expected_hash):
        raise ValueError(f"frozen formula mismatch: {case}")
    cnf_path = directory / formula["name"]
    cnf_hash, cnf_bytes, cnf_lines = universal.sha256_file(cnf_path, count_lines=True)
    if (cnf_hash, cnf_bytes, cnf_lines) != (
        expected_hash,
        expected_bytes,
        expected_clauses + 1,
    ):
        raise ValueError(f"external CNF mismatch: {case}")

    solver = certificate["solver"]
    if solver["sha256"] != SOLVER_SHA256 or tuple(solver["flags"]) != certify.SOLVER_FLAGS:
        raise ValueError(f"solver identity or flags mismatch: {case}")
    if solver["returncode"] != 20 or solver["stop_reason"] is not None:
        raise ValueError(f"solver status mismatch: {case}")
    solver_log_path = case_dir / solver["log"]["name"]
    solver_log = checked_file(solver_log_path, solver["log"], artifact_root)
    solver_text = solver_log_path.read_text(encoding="utf-8", errors="replace")
    if "s UNSATISFIABLE" not in solver_text or "--checkproof=2" not in solver_text:
        raise ValueError(f"solver log lacks checked UNSAT: {case}")

    lrat = certificate["lrat"]
    proof_path = case_dir / lrat["name"]
    proof = checked_file(proof_path, lrat, artifact_root)
    replay = certificate["replay"]
    _, _, theorem = certify.theorem_identity(p, q)
    if replay["theorem"] != theorem or replay["status"] != "LEAN_LRAT_REPLAY_SUCCEEDED":
        raise ValueError(f"Lean theorem identity mismatch: {case}")
    if not certify.axioms_allowed(replay["axioms"], p, q):
        raise ValueError(f"Lean axiom audit failed: {case}")
    lean_path = case_dir / replay["lean_source"]["name"]
    lean_log_path = case_dir / replay["log"]["name"]
    lean_source = checked_file(lean_path, replay["lean_source"], artifact_root)
    lean_log = checked_file(lean_log_path, replay["log"], artifact_root)
    lean_text = lean_log_path.read_text(encoding="utf-8", errors="replace")
    if theorem not in lean_text or "sorryAx" in lean_text:
        raise ValueError(f"Lean replay log mismatch: {case}")

    return {
        "case": [p, q],
        "formula": {
            "name": formula["name"],
            "variables": formula["variables"],
            "clauses": expected_clauses,
            "bytes": expected_bytes,
            "sha256": expected_hash,
            "artifact_path": relative_artifact_path(cnf_path, artifact_root),
        },
        "lrat": {"name": lrat["name"], **proof},
        "solver": {
            "sha256": SOLVER_SHA256,
            "flags": list(certify.SOLVER_FLAGS),
            "conflict_limit": solver["conflict_limit"],
            "metrics": solver["metrics"],
            "elapsed_seconds": solver["elapsed_seconds"],
            "log": solver_log,
        },
        "lean_replay": {
            "status": replay["status"],
            "theorem": theorem,
            "axioms": replay["axioms"],
            "axioms_allowed": True,
            "trim": replay["trim"],
            "wall_seconds": replay["wall_seconds"],
            "lean_source": lean_source,
            "log": lean_log,
        },
        "source_certificate": {
            "bytes": certificate_path.stat().st_size,
            "sha256": sha256(certificate_path),
            "artifact_path": relative_artifact_path(certificate_path, artifact_root),
        },
        "source_batch_manifest": {
            "bytes": batch_path.stat().st_size,
            "sha256": sha256(batch_path),
            "artifact_path": relative_artifact_path(batch_path, artifact_root),
        },
    }


def consolidate(output: Path) -> dict[str, object]:
    output = universal.ensure_ssd(output)
    two.verify(output)
    directory = output / two.OUTPUT_DIRECTORY
    source_manifest = directory / two.SUMMARY_NAME
    if sha256(source_manifest) != SOURCE_MANIFEST_SHA256:
        raise ValueError("two-centre source manifest hash mismatch")
    if set(CASE_DIRECTORIES) != set(two.CASES):
        raise ValueError("certificate directory map does not cover all cases")
    rows = [load_case(directory, case) for case in two.CASES]
    total_lrat_bytes = sum(int(row["lrat"]["bytes"]) for row in rows)

    historical_directory = directory / "p2_q0_cert_v1"
    historical_paths = (
        historical_directory / "cover9_d8_two_center_p2_q0.lrat",
        historical_directory / "cover9_d8_two_center_p2_q0_checked.lrat",
    )
    historical = [
        {
            "artifact_path": relative_artifact_path(path, output),
            "bytes": path.stat().st_size,
            "sha256": sha256(path),
        }
        for path in historical_paths
    ]
    canonical_p2q0 = next(row for row in rows if row["case"] == [2, 0])["lrat"]
    if any(
        (row["bytes"], row["sha256"])
        != (canonical_p2q0["bytes"], canonical_p2q0["sha256"])
        for row in historical
    ):
        raise ValueError("p=2,q=0 deterministic reproductions differ")

    return {
        "schema_version": 2,
        "status": "THIRTEEN_OF_THIRTEEN_EXACT_CNFS_LEAN_LRAT_CERTIFIED",
        "scope": "All 13 labelled two-centre residual CNFs in the degree-eight universal cover9 split are unsatisfiable.",
        "limitations": [
            "The semantic bridge from graph restrictions to the simplified CNFs is not yet formalized in Lean.",
            "This does not certify root degrees 3 through 7.",
            "This is not yet the global universal induced-cover theorem or a new Ramsey-number bound."
        ],
        "artifact_root_policy": {
            "root_argument": "--output",
            "required_storage": "absolute path on drive S:",
            "path_encoding": "artifact_path is POSIX-style relative to --output",
        },
        "source_manifest": {
            "artifact_path": relative_artifact_path(source_manifest, output),
            "sha256": SOURCE_MANIFEST_SHA256,
        },
        "solver": {
            "version": "2.1.2",
            "sha256": SOLVER_SHA256,
            "flags": list(certify.SOLVER_FLAGS),
        },
        "lake_sha256": LAKE_SHA256,
        "certificate_count": len(rows),
        "total_lrat_bytes": total_lrat_bytes,
        "maximum_lrat_bytes": max(int(row["lrat"]["bytes"]) for row in rows),
        "cases": rows,
        "p2_q0_determinism_audit": {
            "identical_generations": 3,
            "canonical": canonical_p2q0,
            "historical": historical,
            "historical_checked_log_sha256": "E576783E7F05278455B965EC91C26EA8F21E68492632563BD0BDCA2DA87A46DF",
            "historical_replay_report_sha256": "CB95B0D3F20546508B8CE97811062F8FD325AEBC0296378F0A79A9B6A2FCBED3"
        },
    }


def verify_manifest(result: dict[str, object], path: Path) -> None:
    if not path.is_file():
        raise FileNotFoundError(path)
    expected = json.loads(path.read_text(encoding="utf-8"))
    if result != expected:
        raise ValueError(f"consolidated manifest mismatch: {path}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True, type=Path)
    action = parser.add_mutually_exclusive_group(required=True)
    action.add_argument("--destination", type=Path)
    action.add_argument("--verify-manifest", type=Path)
    args = parser.parse_args()
    result = consolidate(args.output)
    if args.verify_manifest is not None:
        verify_manifest(result, args.verify_manifest)
        manifest = args.verify_manifest
        action_status = "VERIFIED_EXISTING_MANIFEST"
    else:
        assert args.destination is not None
        if args.destination.exists():
            raise FileExistsError(f"refusing existing manifest: {args.destination}")
        args.destination.write_text(
            json.dumps(result, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
            newline="\n",
        )
        manifest = args.destination
        action_status = "WROTE_NEW_MANIFEST"
    print(
        json.dumps(
            {
                "action": action_status,
                "status": result["status"],
                "certificate_count": result["certificate_count"],
                "total_lrat_bytes": result["total_lrat_bytes"],
                "manifest": str(manifest),
                "manifest_sha256": sha256(manifest),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
