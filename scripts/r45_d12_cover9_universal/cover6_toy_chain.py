#!/usr/bin/env python3
"""Tiny end-to-end induced-cover instance for the cover6 trust chain.

The mathematical statement is deliberately small and non-vacuous:

    every red/blue colouring of K5 with no monochromatic triangle contains
    an induced positive P3 (two positive edges and one negative edge).

The DIMACS formula is the conjunction of the exact R(3,3,5) clauses and one
blocking clause for every injective labelled embedding of that P3.  It is
therefore satisfiable exactly when the theorem has a counterexample.  The
module provides independent exhaustive component checks so that a corrupted
Ramsey clause or motif bridge is detected even though the complete formula is
UNSAT.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path
from typing import Iterable, Sequence


HERE = Path(__file__).resolve().parent
ARTIFACT_DIRECTORY = HERE / "toy_cover6"
DEFAULT_FORMULA = ARTIFACT_DIRECTORY / "cover6_toy_p3.cnf"
DEFAULT_LRAT = ARTIFACT_DIRECTORY / "cover6_toy_p3.lrat"
DEFAULT_MANIFEST = ARTIFACT_DIRECTORY / "MANIFEST.json"

ORDER = 5
VARIABLES = ORDER * (ORDER - 1) // 2
TRIPLES = 10
RAMSEY_CLAUSES = 2 * TRIPLES
P3_EMBEDDINGS = ORDER * (ORDER - 1) * (ORDER - 2)
TOTAL_CLAUSES = RAMSEY_CLAUSES + P3_EMBEDDINGS
EXPECTED_FORMULA_BYTES = 826
EXPECTED_FORMULA_SHA256 = "3B01FC465184466A2B5E9F10966A4E28D3D2CB25D4728B9A1471A5060CC96313"
EXPECTED_LRAT_BYTES = 379
EXPECTED_LRAT_SHA256 = "EDF122CE124CD6FAF367D5989B024D8E41CB18CD7D0EDDAB287DA179B600C4C5"

Clause = tuple[int, ...]
Embedding = tuple[int, int, int]


def edge_var(left: int, right: int) -> int:
    """Zero-based Ramsey edge variable, symmetric in its endpoints."""

    if left == right:
        raise ValueError("loops are not edge variables")
    if left > right:
        left, right = right, left
    if not 0 <= left < right < ORDER:
        raise ValueError("edge endpoint out of range")
    return left * (2 * ORDER - left - 1) // 2 + right - left - 1


def lean_subsets(n: int, size: int) -> tuple[tuple[int, ...], ...]:
    """Exact list order of ``LRATCatcher.Ramsey.subsets``."""

    if size == 0:
        return ((),)
    if n == 0:
        return ()
    return tuple((n - 1, *tail) for tail in lean_subsets(n - 1, size - 1)) + lean_subsets(
        n - 1, size
    )


def clique_edge_vars(vertices: Sequence[int]) -> tuple[int, ...]:
    """Exact literal order of ``LRATCatcher.Ramsey.cliqueEdgeVars``."""

    return tuple(
        edge_var(left, right)
        for left in vertices
        for right in vertices
        if left < right
    )


def ramsey_clauses() -> tuple[Clause, ...]:
    subsets = lean_subsets(ORDER, 3)
    red = tuple(tuple(-(variable + 1) for variable in clique_edge_vars(vertices)) for vertices in subsets)
    blue = tuple(tuple(variable + 1 for variable in clique_edge_vars(vertices)) for vertices in subsets)
    result = red + blue
    if len(result) != RAMSEY_CLAUSES:
        raise RuntimeError("Ramsey clause count changed")
    return result


def p3_embeddings() -> tuple[Embedding, ...]:
    result = tuple(
        (left, center, right)
        for left in range(ORDER)
        for center in range(ORDER)
        for right in range(ORDER)
        if len({left, center, right}) == 3
    )
    if len(result) != P3_EMBEDDINGS:
        raise RuntimeError("P3 embedding count changed")
    return result


def p3_blocker(embedding: Embedding) -> Clause:
    """Negation of one exact induced positive path ``left-center-right``."""

    left, center, right = embedding
    if len({left, center, right}) != 3:
        raise ValueError("P3 embedding must be injective")
    return (
        -(edge_var(left, center) + 1),
        -(edge_var(center, right) + 1),
        edge_var(left, right) + 1,
    )


def motif_blockers() -> tuple[Clause, ...]:
    return tuple(p3_blocker(embedding) for embedding in p3_embeddings())


def formula_clauses() -> tuple[Clause, ...]:
    result = ramsey_clauses() + motif_blockers()
    if len(result) != TOTAL_CLAUSES:
        raise RuntimeError("toy formula clause count changed")
    return result


def formula_bytes(clauses: Sequence[Clause] | None = None) -> bytes:
    selected = formula_clauses() if clauses is None else tuple(clauses)
    body = "".join(" ".join(map(str, clause)) + " 0\n" for clause in selected)
    return f"p cnf {VARIABLES} {len(selected)}\n".encode("ascii") + body.encode("ascii")


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def value(mask: int, variable: int) -> bool:
    if not 1 <= variable <= VARIABLES:
        raise ValueError(f"DIMACS variable out of range: {variable}")
    return bool(mask >> (variable - 1) & 1)


def eval_clause(mask: int, clause: Sequence[int]) -> bool:
    return any(value(mask, abs(literal)) == (literal > 0) for literal in clause)


def eval_cnf(mask: int, clauses: Iterable[Sequence[int]]) -> bool:
    return all(eval_clause(mask, clause) for clause in clauses)


def is_r33_free(mask: int) -> bool:
    for vertices in itertools.combinations(range(ORDER), 3):
        edges = sum(bool(mask >> edge_var(*pair) & 1) for pair in itertools.combinations(vertices, 2))
        if edges in (0, 3):
            return False
    return True


def has_induced_positive_p3(mask: int) -> bool:
    return any(
        bool(mask >> edge_var(left, center) & 1)
        and bool(mask >> edge_var(center, right) & 1)
        and not bool(mask >> edge_var(left, right) & 1)
        for left, center, right in p3_embeddings()
    )


def first_component_mismatch(
    base: Sequence[Clause], blockers: Sequence[Clause]
) -> dict[str, int | bool] | None:
    """Return the first semantic mismatch for either independently checked block."""

    for mask in range(1 << VARIABLES):
        observed_base = eval_cnf(mask, base)
        expected_base = is_r33_free(mask)
        if observed_base != expected_base:
            return {
                "component": 0,
                "mask": mask,
                "observed": observed_base,
                "expected": expected_base,
            }
        observed_blockers = eval_cnf(mask, blockers)
        expected_blockers = not has_induced_positive_p3(mask)
        if observed_blockers != expected_blockers:
            return {
                "component": 1,
                "mask": mask,
                "observed": observed_blockers,
                "expected": expected_blockers,
            }
    return None


def preflight() -> dict[str, object]:
    base = ramsey_clauses()
    blockers = motif_blockers()
    mismatch = first_component_mismatch(base, blockers)
    if mismatch is not None:
        raise RuntimeError(f"toy component semantics mismatch: {mismatch}")
    ramsey_free_models = [
        mask for mask in range(1 << VARIABLES) if is_r33_free(mask)
    ]
    counterexamples = [
        mask for mask in ramsey_free_models if not has_induced_positive_p3(mask)
    ]
    if len(ramsey_free_models) != 12:
        raise RuntimeError(
            f"toy non-vacuity count changed: {len(ramsey_free_models)}"
        )
    if counterexamples:
        raise RuntimeError(f"toy theorem has counterexamples: {counterexamples[:4]}")
    payload = formula_bytes(base + blockers)
    return {
        "status": "PASS",
        "statement": "Every R(3,3)-free graph on five vertices contains an induced positive P3.",
        "variables": VARIABLES,
        "ramsey_clauses": len(base),
        "p3_embedding_blockers": len(blockers),
        "clauses": len(base) + len(blockers),
        "bytes": len(payload),
        "sha256": sha256_bytes(payload),
        "assignments_checked": 1 << VARIABLES,
        "ramsey_free_models": len(ramsey_free_models),
        "counterexamples": len(counterexamples),
        "component_semantics_exact": True,
    }


def parse_dimacs(payload: bytes) -> tuple[Clause, ...]:
    lines = payload.decode("ascii").splitlines()
    if not lines:
        raise ValueError("empty DIMACS payload")
    header = lines[0].split()
    if len(header) != 4 or header[:3] != ["p", "cnf", str(VARIABLES)]:
        raise ValueError("unexpected DIMACS header")
    expected = int(header[3])
    clauses = []
    for line_number, line in enumerate(lines[1:], 2):
        values = tuple(map(int, line.split()))
        if not values or values[-1] != 0 or 0 in values[:-1]:
            raise ValueError(f"malformed DIMACS clause at line {line_number}")
        clause = values[:-1]
        if any(not 1 <= abs(literal) <= VARIABLES for literal in clause):
            raise ValueError(f"literal out of range at line {line_number}")
        if len(set(clause)) != len(clause) or any(-literal in clause for literal in clause):
            raise ValueError(f"duplicate or tautological clause at line {line_number}")
        clauses.append(clause)
    if len(clauses) != expected:
        raise ValueError(f"DIMACS clause count mismatch: {len(clauses)} != {expected}")
    return tuple(clauses)


def verify_formula_payload(payload: bytes, *, source: str = "<memory>") -> dict[str, object]:
    parsed = parse_dimacs(payload)
    expected = formula_clauses()
    if parsed != expected:
        raise ValueError(
            f"{source}: DIMACS clauses differ from the independently reconstructed toy formula"
        )
    report = preflight()
    if report["sha256"] != sha256_bytes(payload) or report["bytes"] != len(payload):
        raise ValueError(f"{source}: DIMACS byte identity mismatch")
    if (len(payload), sha256_bytes(payload)) != (
        EXPECTED_FORMULA_BYTES,
        EXPECTED_FORMULA_SHA256,
    ):
        raise ValueError(f"{source}: frozen DIMACS identity mismatch")
    return {"status": "PASS", "source": source, **report}


def verify_artifact(path: Path = DEFAULT_FORMULA) -> dict[str, object]:
    return verify_formula_payload(path.read_bytes(), source=str(path))


def verify_lrat_payload(payload: bytes, *, source: str = "<memory>") -> dict[str, object]:
    observed = (len(payload), sha256_bytes(payload))
    expected = (EXPECTED_LRAT_BYTES, EXPECTED_LRAT_SHA256)
    if observed != expected:
        raise ValueError(f"{source}: frozen LRAT identity mismatch")
    return {
        "status": "PASS",
        "source": source,
        "bytes": observed[0],
        "sha256": observed[1],
    }


def verify_lrat(path: Path = DEFAULT_LRAT) -> dict[str, object]:
    return verify_lrat_payload(path.read_bytes(), source=str(path))


def checked_identity(path: Path, expected_bytes: int, expected_sha256: str) -> None:
    observed = (path.stat().st_size, sha256_bytes(path.read_bytes()))
    expected = (expected_bytes, expected_sha256)
    if observed != expected:
        raise ValueError(f"frozen identity mismatch for {path}: {observed} != {expected}")


def verify_manifest(path: Path = DEFAULT_MANIFEST) -> dict[str, object]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("schema_version") != 1 or data.get("proof_level") != 4:
        raise ValueError("unexpected toy manifest schema or proof level")
    encoding = data.get("encoding", {})
    expected_encoding = {
        "variables": VARIABLES,
        "ramsey_clauses": RAMSEY_CLAUSES,
        "injective_p3_embedding_blockers": P3_EMBEDDINGS,
        "clauses": TOTAL_CLAUSES,
        "exhaustive_assignments_checked": 1 << VARIABLES,
        "ramsey_free_models": 12,
        "counterexamples": 0,
        "component_semantics_exact": True,
    }
    if encoding != expected_encoding:
        raise ValueError("toy manifest encoding summary changed")

    formula_entry = data["artifacts"]["cnf"]
    formula_path = (path.parent / formula_entry["name"]).resolve()
    checked_identity(formula_path, formula_entry["bytes"], formula_entry["sha256"])
    formula_report = verify_artifact(formula_path)

    lrat_entry = data["artifacts"]["lrat"]
    lrat_path = (path.parent / lrat_entry["name"]).resolve()
    checked_identity(lrat_path, lrat_entry["bytes"], lrat_entry["sha256"])
    lrat_report = verify_lrat(lrat_path)

    lean_entry = data["lean"]
    lean_path = (path.parent / lean_entry["source"]).resolve()
    checked_identity(
        lean_path, lean_entry["source_bytes"], lean_entry["source_sha256"]
    )
    program_entry = data["program"]
    program_path = (path.parent / program_entry["name"]).resolve()
    if program_path != Path(__file__).resolve():
        raise ValueError("toy manifest program path does not identify this verifier")
    checked_identity(
        program_path, program_entry["bytes"], program_entry["sha256"]
    )
    return {
        "status": "PASS",
        "manifest": str(path.resolve()),
        "formula": formula_report,
        "lrat": lrat_report,
        "lean_source": str(lean_path),
        "program": str(program_path),
        "all_manifest_identities_exact": True,
    }


def generate(path: Path) -> dict[str, object]:
    if path.exists():
        raise FileExistsError(f"refusing to replace toy artifact: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = formula_bytes()
    path.write_bytes(payload)
    return verify_artifact(path)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("preflight", "generate", "verify"))
    parser.add_argument("--formula", type=Path, default=DEFAULT_FORMULA)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    args = parser.parse_args()
    if args.command == "preflight":
        report = preflight()
    elif args.command == "generate":
        report = generate(args.formula)
    else:
        report = verify_manifest(args.manifest)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
