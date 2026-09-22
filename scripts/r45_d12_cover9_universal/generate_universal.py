#!/usr/bin/env python3
"""Generate a catalogue-independent SAT target for the cover9 theorem.

The 66 variables are the edges of K_12.  The formula first excludes a K4
in either colour.  It then excludes every induced labelled occurrence of the
nine order-seven patterns in ``../r45_d12_structural_cover/cover9.tsv``.

The literal-by-literal encoding would need 26,460 * C(12,7) blockers.  Six
frozen partial-pattern representatives give an equivalent, smaller encoding:
an exhaustive check of all 2^21 labelled graphs on seven vertices verifies
that, modulo the local R(4,4) clauses, their permutation closures reject
exactly those same 26,460 patterns.

The CLI only writes large artifacts below an absolute S: path.  It invokes no
SAT solver and does not use the R(4,4,12) catalogue.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import os
from collections import Counter
from pathlib import Path, PureWindowsPath
from typing import BinaryIO, Iterable, Iterator, Sequence


HERE = Path(__file__).resolve().parent
COVER_PATH = HERE.parent / "r45_d12_structural_cover" / "cover9.tsv"

ORDER = 12
MOTIF_ORDER = 7
VARIABLE_COUNT = ORDER * (ORDER - 1) // 2
LOCAL_VARIABLE_COUNT = MOTIF_ORDER * (MOTIF_ORDER - 1) // 2
SUBSET_COUNT = 792
BASE_CLAUSE_COUNT = 990
RAW_LABELLED_PATTERN_COUNT = 26_460
RAW_BLOCKER_COUNT = RAW_LABELLED_PATTERN_COUNT * SUBSET_COUNT
RAW_CLAUSE_COUNT = BASE_CLAUSE_COUNT + RAW_BLOCKER_COUNT

COVER_RECORDS = (
    "FiIXw",
    "FANbw",
    "F@Y]w",
    "FqhXw",
    "FFhmw",
    "FqHXw",
    "FQl~_",
    "FIiZw",
    "Fqoxw",
)
COVER_SHA256 = "5A2B4F3824FFFEF9BC6048C0B881F5BC7E2C90D85024485422C7A9B096EF5B12"
RAW_ORBIT_COUNTS = (5_040, 2_520, 5_040, 2_520, 2_520, 2_520, 2_520, 2_520, 1_260)

# (ones, fixed): a local assignment matches a cube iff
# ``assignment & fixed == ones``.  These representatives were expanded only
# through vertex permutations; their exactness is rechecked exhaustively.
REDUCED_CUBE_REPRESENTATIVES = (
    (0x2964E, 0x39EDF),
    (0x3EF43, 0x3EF73),
    (0x3846A, 0x3EEEF),
    (0x2AF9C, 0x7BFDE),
    (0x3AFE1, 0x7BFFF),
    (0x1C75C, 0x7DFFF),
)
REDUCED_ORBIT_COUNTS = (1_260, 2_520, 2_520, 2_520, 1_260, 5_040)
REDUCED_LOCAL_CLAUSE_COUNT = 15_120
REDUCED_CLAUSE_COUNT = BASE_CLAUSE_COUNT + REDUCED_LOCAL_CLAUSE_COUNT * SUBSET_COUNT
EXPECTED_LOCAL_R44_COUNT = 923_012
EXPECTED_LOCAL_ALLOWED_COUNT = 896_552

# Frozen after the first independent generation.  ``None`` means that only
# the manifest hash (plus structural verification) is checked.
EXPECTED_LOCAL_TEMPLATE_SHA256: str | None = "E10B250F2198A569C0A18FDF817B3072CF1266A6B532100AD20F53308296947D"
EXPECTED_FORMULA_SHA256: str | None = "425676A0876F06BCE2D3477BB6D11A566D77C6DD7D7FD46E9A1B07D8E5C1C098"
EXPECTED_FORMULA_BYTES: int | None = 701_106_138

Clause = tuple[int, ...]
Cube = tuple[int, int]


def sha256_file(path: Path, *, count_lines: bool = False) -> tuple[str, int, int | None]:
    digest = hashlib.sha256()
    size = 0
    lines = 0
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(block)
            size += len(block)
            if count_lines:
                lines += block.count(b"\n")
    return digest.hexdigest().upper(), size, lines if count_lines else None


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def ensure_ssd(path: Path) -> Path:
    parsed = PureWindowsPath(str(path))
    if not parsed.is_absolute() or parsed.drive.upper() != "S:":
        raise ValueError(f"large artifact directory must be absolute on S:, got {path}")
    return path


def edge_position(left: int, right: int) -> int:
    """Zero-based graph6 (column-major upper triangle) edge position."""
    if left > right:
        left, right = right, left
    if left == right or left < 0:
        raise ValueError("not an edge")
    return right * (right - 1) // 2 + left


def edge_var(order: int, left: int, right: int) -> int:
    """One-based row-major upper-triangle DIMACS variable."""
    if left > right:
        left, right = right, left
    if not 0 <= left < right < order:
        raise ValueError(f"not an edge of K_{order}: ({left},{right})")
    return left * (2 * order - left - 1) // 2 + right - left


def decode_short_graph6_mask(record: str, order: int = MOTIF_ORDER) -> int:
    """Decode a short graph6 record into graph6 edge-position bits."""
    record = record.strip()
    if not record or ord(record[0]) - 63 != order:
        raise ValueError(f"wrong graph6 order: {record!r}")
    edge_count = order * (order - 1) // 2
    payload_count = (edge_count + 5) // 6
    if len(record) != 1 + payload_count:
        raise ValueError(f"wrong graph6 payload length: {record!r}")
    result = 0
    position = 0
    for char in record[1:]:
        value = ord(char) - 63
        if not 0 <= value < 64:
            raise ValueError(f"invalid graph6 character: {record!r}")
        for bit in range(5, -1, -1):
            if position < edge_count and (value >> bit) & 1:
                result |= 1 << position
            position += 1
    if any((ord(char) - 63) & ((1 << (position - edge_count)) - 1) for char in record[-1:]):
        raise ValueError(f"non-zero graph6 padding: {record!r}")
    return result


def read_cover_records() -> tuple[str, ...]:
    digest, _size, _lines = sha256_file(COVER_PATH)
    if digest != COVER_SHA256:
        raise ValueError(f"cover9.tsv SHA-256 mismatch: {digest}")
    records: list[str] = []
    for line in COVER_PATH.read_text(encoding="ascii").splitlines():
        if not line or line.startswith("#"):
            continue
        order, record = line.split()
        if order != str(MOTIF_ORDER):
            raise ValueError("cover9 contains a non-order-seven record")
        records.append(record)
    result = tuple(records)
    if result != COVER_RECORDS:
        raise ValueError("cover9 record sequence changed")
    return result


def relabel_mask(mask: int, permutation: Sequence[int]) -> int:
    result = 0
    target_position = 0
    for right in range(1, len(permutation)):
        for left in range(right):
            source_position = edge_position(permutation[left], permutation[right])
            if (mask >> source_position) & 1:
                result |= 1 << target_position
            target_position += 1
    return result


def labelled_orbit(mask: int) -> frozenset[int]:
    return frozenset(
        relabel_mask(mask, permutation)
        for permutation in itertools.permutations(range(MOTIF_ORDER))
    )


def raw_forbidden_masks() -> frozenset[int]:
    records = read_cover_records()
    orbits = tuple(labelled_orbit(decode_short_graph6_mask(record)) for record in records)
    counts = tuple(len(orbit) for orbit in orbits)
    if counts != RAW_ORBIT_COUNTS:
        raise RuntimeError(f"raw orbit counts changed: {counts}")
    union = frozenset().union(*orbits)
    if len(union) != RAW_LABELLED_PATTERN_COUNT:
        raise RuntimeError(f"raw labelled closure changed: {len(union)}")
    return union


def relabel_cube(cube: Cube, permutation: Sequence[int]) -> Cube:
    ones, fixed = cube
    return relabel_mask(ones, permutation), relabel_mask(fixed, permutation)


def reduced_cubes() -> tuple[Cube, ...]:
    permutations = tuple(itertools.permutations(range(MOTIF_ORDER)))
    orbits = tuple(
        frozenset(relabel_cube(cube, permutation) for permutation in permutations)
        for cube in REDUCED_CUBE_REPRESENTATIVES
    )
    counts = tuple(len(orbit) for orbit in orbits)
    if counts != REDUCED_ORBIT_COUNTS:
        raise RuntimeError(f"reduced cube orbit counts changed: {counts}")
    union = frozenset().union(*orbits)
    if len(union) != REDUCED_LOCAL_CLAUSE_COUNT:
        raise RuntimeError(f"reduced cube union changed: {len(union)}")
    for ones, fixed in union:
        if ones & ~fixed:
            raise RuntimeError("cube has a one on a free edge")
    return tuple(sorted(union, key=lambda cube: (cube[1].bit_count(), cube[1], cube[0])))


def local_k4_masks() -> tuple[int, ...]:
    return tuple(
        sum(
            1 << edge_position(left, right)
            for left, right in itertools.combinations(vertices, 2)
        )
        for vertices in itertools.combinations(range(MOTIF_ORDER), 4)
    )


def is_local_r44(mask: int, clique_masks: Sequence[int] | None = None) -> bool:
    cliques = local_k4_masks() if clique_masks is None else clique_masks
    return all((mask & clique) not in (0, clique) for clique in cliques)


def validate_local_reduction() -> dict[str, object]:
    """Exhaustively prove equivalence of raw and reduced local blockers."""
    forbidden = raw_forbidden_masks()
    cubes = reduced_cubes()
    cliques = local_k4_masks()
    local_limit = 1 << LOCAL_VARIABLE_COUNT
    r44 = bytearray(local_limit)
    r44_count = 0
    for mask in range(local_limit):
        if is_local_r44(mask, cliques):
            r44[mask] = 1
            r44_count += 1
    if r44_count != EXPECTED_LOCAL_R44_COUNT:
        raise RuntimeError(f"local R(4,4) count changed: {r44_count}")

    rejected: set[int] = set()
    full = local_limit - 1
    for ones, fixed in cubes:
        free = full ^ fixed
        completion = free
        while True:
            mask = ones | completion
            if r44[mask]:
                if mask not in forbidden:
                    raise RuntimeError(
                        f"reduced cube rejects an allowed local graph: {mask:#x}"
                    )
                rejected.add(mask)
            if completion == 0:
                break
            completion = (completion - 1) & free
    if rejected != forbidden:
        missing = forbidden - rejected
        raise RuntimeError(f"reduced cubes miss {len(missing)} forbidden assignments")

    width_counts = Counter(fixed.bit_count() for _ones, fixed in cubes)
    expected_widths = {14: 3_780, 15: 2_520, 16: 2_520, 18: 6_300}
    if dict(width_counts) != expected_widths:
        raise RuntimeError(f"reduced width distribution changed: {dict(width_counts)}")
    supports = Counter()
    for _ones, fixed in cubes:
        vertices: set[int] = set()
        for right in range(1, MOTIF_ORDER):
            for left in range(right):
                if (fixed >> edge_position(left, right)) & 1:
                    vertices.update((left, right))
        supports[len(vertices)] += 1
    if supports != {MOTIF_ORDER: REDUCED_LOCAL_CLAUSE_COUNT}:
        raise RuntimeError(f"some reduced clauses do not use all seven vertices: {supports}")

    return {
        "status": "PASS",
        "checked_assignments": local_limit,
        "r44_assignments": r44_count,
        "raw_forbidden_assignments": len(forbidden),
        "reduced_rejected_assignments_under_r44": len(rejected),
        "allowed_assignments_under_r44": r44_count - len(rejected),
        "raw_orbit_counts": list(RAW_ORBIT_COUNTS),
        "reduced_representatives": [
            {"ones": f"0x{ones:X}", "fixed": f"0x{fixed:X}"}
            for ones, fixed in REDUCED_CUBE_REPRESENTATIVES
        ],
        "reduced_orbit_counts": list(REDUCED_ORBIT_COUNTS),
        "reduced_clause_widths": dict(sorted(width_counts.items())),
        "reduced_local_clauses": len(cubes),
        "all_reduced_clauses_use_seven_vertices": True,
        "equivalence": (
            "For every labelled seven-vertex assignment satisfying local "
            "R(4,4), a reduced cube matches iff the assignment belongs to "
            "the union of the nine complete labelled motif orbits."
        ),
    }


def ramsey_clauses(order: int = ORDER) -> Iterator[Clause]:
    subsets = tuple(itertools.combinations(range(order), 4))
    for vertices in subsets:
        yield tuple(-edge_var(order, left, right) for left, right in itertools.combinations(vertices, 2))
    for vertices in subsets:
        yield tuple(edge_var(order, left, right) for left, right in itertools.combinations(vertices, 2))


def subset_variables(vertices: Sequence[int], order: int = ORDER) -> tuple[int, ...]:
    if len(vertices) != MOTIF_ORDER or tuple(sorted(vertices)) != tuple(vertices):
        raise ValueError("expected seven distinct increasing vertices")
    return tuple(
        edge_var(order, vertices[left], vertices[right])
        for right in range(1, MOTIF_ORDER)
        for left in range(right)
    )


def instantiate_cube_blocker(cube: Cube, variables: Sequence[int]) -> Clause:
    if len(variables) != LOCAL_VARIABLE_COUNT:
        raise ValueError("expected 21 local-to-global variables")
    ones, fixed = cube
    return tuple(
        -variables[position] if (ones >> position) & 1 else variables[position]
        for position in range(LOCAL_VARIABLE_COUNT)
        if (fixed >> position) & 1
    )


def local_template_bytes(cubes: Sequence[Cube] | None = None) -> bytes:
    selected = reduced_cubes() if cubes is None else tuple(cubes)
    variables = tuple(range(1, LOCAL_VARIABLE_COUNT + 1))
    lines = [f"p cnf {LOCAL_VARIABLE_COUNT} {len(selected)}\n"]
    lines.extend(
        " ".join(map(str, instantiate_cube_blocker(cube, variables))) + " 0\n"
        for cube in selected
    )
    return "".join(lines).encode("ascii")


def formula_clause_count() -> int:
    if len(tuple(itertools.combinations(range(ORDER), MOTIF_ORDER))) != SUBSET_COUNT:
        raise RuntimeError("K12 seven-subset count changed")
    if 2 * len(tuple(itertools.combinations(range(ORDER), 4))) != BASE_CLAUSE_COUNT:
        raise RuntimeError("K12 R(4,4) clause count changed")
    return REDUCED_CLAUSE_COUNT


def exact_formula_byte_count(cubes: Sequence[Cube] | None = None) -> int:
    """Compute the exact deterministic DIMACS size without rendering it."""
    selected = reduced_cubes() if cubes is None else tuple(cubes)
    zero_occurrences = [0] * LOCAL_VARIABLE_COUNT
    one_occurrences = [0] * LOCAL_VARIABLE_COUNT
    literal_count = 0
    for ones, fixed in selected:
        for position in range(LOCAL_VARIABLE_COUNT):
            if (fixed >> position) & 1:
                literal_count += 1
                target = one_occurrences if (ones >> position) & 1 else zero_occurrences
                target[position] += 1
    result = len(f"p cnf {VARIABLE_COUNT} {REDUCED_CLAUSE_COUNT}\n".encode("ascii"))
    result += sum(
        len(" ".join(map(str, clause)) + " 0\n") for clause in ramsey_clauses()
    )
    punctuation_bytes_per_subset = literal_count + 2 * len(selected)
    for vertices in itertools.combinations(range(ORDER), MOTIF_ORDER):
        variables = subset_variables(vertices)
        result += punctuation_bytes_per_subset
        result += sum(
            zero_occurrences[position] * len(str(variable))
            + one_occurrences[position] * (len(str(variable)) + 1)
            for position, variable in enumerate(variables)
        )
    return result

def _write_block(stream: BinaryIO, digest: "hashlib._Hash", data: bytes) -> int:
    stream.write(data)
    digest.update(data)
    return len(data)


def write_formula(path: Path, cubes: Sequence[Cube]) -> dict[str, object]:
    clause_count = formula_clause_count()
    digest = hashlib.sha256()
    byte_count = 0
    written_clauses = 0
    with path.open("xb", buffering=8 * 1024 * 1024) as stream:
        header = f"p cnf {VARIABLE_COUNT} {clause_count}\n".encode("ascii")
        byte_count += _write_block(stream, digest, header)
        base_lines = "".join(
            " ".join(map(str, clause)) + " 0\n" for clause in ramsey_clauses()
        ).encode("ascii")
        byte_count += _write_block(stream, digest, base_lines)
        written_clauses += BASE_CLAUSE_COUNT

        compiled = tuple(
            tuple(
                (position, bool((ones >> position) & 1))
                for position in range(LOCAL_VARIABLE_COUNT)
                if (fixed >> position) & 1
            )
            for ones, fixed in cubes
        )
        for subset_index, vertices in enumerate(
            itertools.combinations(range(ORDER), MOTIF_ORDER), 1
        ):
            variables = subset_variables(vertices)
            tokens = tuple((str(variable), f"-{variable}") for variable in variables)
            buffer: list[str] = []
            for spec in compiled:
                buffer.append(
                    " ".join(tokens[position][1 if one else 0] for position, one in spec)
                    + " 0\n"
                )
                if len(buffer) == 4_096:
                    block = "".join(buffer).encode("ascii")
                    byte_count += _write_block(stream, digest, block)
                    buffer.clear()
            if buffer:
                block = "".join(buffer).encode("ascii")
                byte_count += _write_block(stream, digest, block)
            written_clauses += len(compiled)
            if subset_index % 48 == 0 or subset_index == SUBSET_COUNT:
                print(
                    f"generated subsets {subset_index}/{SUBSET_COUNT}; "
                    f"clauses {written_clauses}/{clause_count}; "
                    f"bytes {byte_count}",
                    flush=True,
                )
    if written_clauses != clause_count:
        raise RuntimeError(f"clause count mismatch: {written_clauses} != {clause_count}")
    expected_bytes = exact_formula_byte_count(cubes)
    if byte_count != expected_bytes:
        raise RuntimeError(f"byte count mismatch: {byte_count} != {expected_bytes}")
    return {
        "name": path.name,
        "bytes": byte_count,
        "sha256": digest.hexdigest().upper(),
        "variables": VARIABLE_COUNT,
        "clauses": written_clauses,
    }


def build_manifest(formula: dict[str, object], local: dict[str, object], audit: dict[str, object]) -> dict[str, object]:
    return {
        "schema_version": 1,
        "status": "UNCERTIFIED_SOLVER_TARGET",
        "scope": (
            "Catalogue-independent SAT encoding of a counterexample to the "
            "nine-pattern induced cover of R(4,4,12); no UNSAT proof is "
            "claimed by generation alone."
        ),
        "catalogue_independence": {
            "uses_r44_12_catalogue": False,
            "uses_r44_7_catalogue": False,
            "inputs": ["the nine frozen graph6 records in cover9.tsv"],
        },
        "color_convention": "positive DIMACS edge = raw graph6 adjacency",
        "cover": {
            "path": str(COVER_PATH),
            "sha256": COVER_SHA256,
            "records": list(COVER_RECORDS),
            "raw_labelled_union": RAW_LABELLED_PATTERN_COUNT,
        },
        "encoding": {
            "vertices": ORDER,
            "edge_variables": VARIABLE_COUNT,
            "seven_vertex_subsets": SUBSET_COUNT,
            "base_r44_clauses": BASE_CLAUSE_COUNT,
            "raw_exact_blockers": RAW_BLOCKER_COUNT,
            "raw_total_clauses": RAW_CLAUSE_COUNT,
            "reduced_local_blockers": REDUCED_LOCAL_CLAUSE_COUNT,
            "reduced_total_clauses": REDUCED_CLAUSE_COUNT,
            "reduction_ratio": REDUCED_CLAUSE_COUNT / RAW_CLAUSE_COUNT,
        },
        "local_equivalence_audit": audit,
        "files": {"formula": formula, "local_template": local},
        "proof_status": {
            "solver_run": False,
            "unsat": False,
            "lrat_present": False,
            "publication_claim": False,
        },
    }


def generate(output_directory: Path) -> dict[str, object]:
    output_directory = ensure_ssd(output_directory)
    output_directory.mkdir(parents=True, exist_ok=True)
    formula_path = output_directory / "cover9_universal.cnf"
    template_path = output_directory / "cover9_local_reduced.cnf"
    manifest_path = output_directory / "manifest.json"
    for path in (formula_path, template_path, manifest_path):
        if path.exists():
            raise FileExistsError(f"refusing to replace existing artifact: {path}")

    audit = validate_local_reduction()
    cubes = reduced_cubes()
    template = local_template_bytes(cubes)
    template_path.write_bytes(template)
    local = {
        "name": template_path.name,
        "bytes": len(template),
        "sha256": sha256_bytes(template),
        "variables": LOCAL_VARIABLE_COUNT,
        "clauses": len(cubes),
    }
    partial = output_directory / f"cover9_universal.cnf.{os.getpid()}.partial"
    try:
        formula = write_formula(partial, cubes)
        formula["name"] = formula_path.name
        os.replace(partial, formula_path)
    finally:
        if partial.exists():
            partial.unlink()
    manifest = build_manifest(formula, local, audit)
    manifest_path.write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )
    return manifest


def verify(output_directory: Path) -> dict[str, object]:
    output_directory = ensure_ssd(output_directory)
    manifest_path = output_directory / "manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    if manifest.get("schema_version") != 1:
        raise ValueError("unsupported manifest schema")
    audit = validate_local_reduction()
    normalized_audit = json.loads(json.dumps(audit, sort_keys=True))
    if manifest.get("local_equivalence_audit") != normalized_audit:
        raise ValueError("local equivalence audit mismatch")
    result: dict[str, object] = {"status": "PASS", "files": {}}
    for key, expected_lines in (
        ("formula", REDUCED_CLAUSE_COUNT + 1),
        ("local_template", REDUCED_LOCAL_CLAUSE_COUNT + 1),
    ):
        metadata = manifest["files"][key]
        path = output_directory / metadata["name"]
        digest, size, lines = sha256_file(path, count_lines=True)
        if digest != metadata["sha256"] or size != metadata["bytes"]:
            raise ValueError(f"{key} hash or size mismatch")
        if lines != expected_lines:
            raise ValueError(f"{key} line count mismatch: {lines} != {expected_lines}")
        result["files"][key] = {"sha256": digest, "bytes": size, "lines": lines}
    formula = result["files"]["formula"]
    local = result["files"]["local_template"]
    if EXPECTED_FORMULA_SHA256 is not None and formula["sha256"] != EXPECTED_FORMULA_SHA256:
        raise ValueError("formula differs from frozen SHA-256")
    if EXPECTED_FORMULA_BYTES is not None and formula["bytes"] != EXPECTED_FORMULA_BYTES:
        raise ValueError("formula differs from frozen byte count")
    if EXPECTED_LOCAL_TEMPLATE_SHA256 is not None and local["sha256"] != EXPECTED_LOCAL_TEMPLATE_SHA256:
        raise ValueError("local template differs from frozen SHA-256")
    result["local_equivalence_audit"] = audit
    return result


def preflight() -> dict[str, object]:
    audit = validate_local_reduction()
    template = local_template_bytes()
    return {
        "status": "PASS",
        "formula": {
            "variables": VARIABLE_COUNT,
            "clauses": formula_clause_count(),
            "bytes": exact_formula_byte_count(),
            "raw_unreduced_clauses": RAW_CLAUSE_COUNT,
        },
        "local_template": {
            "bytes": len(template),
            "sha256": sha256_bytes(template),
            "clauses": REDUCED_LOCAL_CLAUSE_COUNT,
        },
        "audit": audit,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("preflight")
    generate_parser = subparsers.add_parser("generate")
    generate_parser.add_argument("--output", required=True, type=Path)
    verify_parser = subparsers.add_parser("verify")
    verify_parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    if args.command == "preflight":
        result = preflight()
    elif args.command == "generate":
        result = generate(args.output)
    else:
        result = verify(args.output)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
