#!/usr/bin/env python3
"""Build and audit the complement closure of the structural cover5 motifs.

The computation is entirely local on seven vertices.  It writes no K12 CNF,
invokes no solver, and makes no UNSAT or global-minimality claim.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import itertools
import json
from array import array
from collections import Counter
from pathlib import Path
from typing import Iterable, Sequence


HERE = Path(__file__).resolve().parent
COVER_PATH = HERE.parent / "r45_d12_gluing_aware_cover" / "cover5_order7.tsv"

N = 7
EDGE_COUNT = 21
LIMIT = 1 << EDGE_COUNT
FULL = LIMIT - 1
Cube = tuple[int, int]

EXPECTED_COVER_SHA256 = (
    "CEAE61F737722C6D1392B5C8D654FC1B09D482AA3C76222EE2D9CBFF3CA5E288"
)
EXPECTED_RECORDS = ("F@h^g", "FCUrO", "FDLmW", "FG`Xo", "FdW}w")
EXPECTED_R44 = 923_012
EXPECTED_RAW_CLOSURE = 17_640
EXPECTED_COMPLEMENT_INTERSECTION = 5_040
EXPECTED_COMPLEMENT_CLOSURE = 30_240
EXPECTED_ISOMORPHISM_CLASSES = 8
EXPECTED_CUBE_ORBITS = 6
EXPECTED_CUBES = 20_160
EXPECTED_WIDTHS = {15: 5_040, 16: 10_080, 19: 5_040}
EXPECTED_RAW_ORBIT_SIZES = (5_040, 2_520, 5_040, 2_520, 2_520)
EXPECTED_CLASS_REPRESENTATIVES = (
    "FpTc?",
    "FNtc?",
    "F\\Ue?",
    "FRUe?",
    "Flue?",
    "Ff]e?",
    "FP~V?",
    "F^U^?",
)
EXPECTED_CLASS_ORBIT_SIZES = (2_520, 5_040, 5_040, 2_520, 5_040, 5_040, 2_520, 2_520)
EXPECTED_INITIAL_CLASS_CUBES = (
    (0x48, 0x7DEDE),
    (0x1CE4C, 0x7DEFE),
    (0x60632, 0x7DEFE),
    (0xA496, 0xFFDFF),
    (0x6106C, 0x7DEFE),
    (0x1CE4C, 0x7DEFE),
    (0x5ED6C, 0xFFDFF),
    (0x6DECE, 0x7DEDE),
)
CUBE_REPRESENTATIVES = (
    (0x3, 0xDF677),
    (0x3E6BE, 0x1BE6BE),
    (0x84AE, 0x19F5BF),
    (0x8DBC, 0x1DCDFE),
    (0x3AFE2, 0x17FFF7),
    (0x88EC, 0x1BEFFF),
)
EXPECTED_CUBE_ORBIT_SIZES = (2_520, 2_520, 5_040, 5_040, 2_520, 2_520)
EXPECTED_ORBIT_REMOVAL_MISSES = (2_520, 2_520, 10_080, 10_080, 2_520, 2_520)
EXPECTED_RAW_CLOSURE_SHA256 = (
    "7D9C82BAA06CC6FB778ED24643E63E58D50594F13D11D4D49E8E0BE14DE578E2"
)
EXPECTED_CLOSED_CLOSURE_SHA256 = (
    "DC2CBCDA3F5D51BE6141B975AA440E51D9F85D6CF1337E4597EDADDF445E227A"
)
EXPECTED_CUBE_CLOSURE_SHA256 = (
    "5E965F8913D4F35391D1C1A3D4890122A19D8D711E4329806B108A39B609EDB7"
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def edge_position(left: int, right: int) -> int:
    if left == right:
        raise ValueError("loops are not graph edges")
    if left > right:
        left, right = right, left
    return right * (right - 1) // 2 + left


def decode_graph6(record: str) -> int:
    if len(record) != 5 or ord(record[0]) - 63 != N:
        raise ValueError(f"invalid order-seven graph6 record: {record!r}")
    mask = 0
    position = 0
    for character in record[1:]:
        value = ord(character) - 63
        if not 0 <= value < 64:
            raise ValueError(f"invalid graph6 character: {record!r}")
        for shift in range(5, -1, -1):
            bit = value >> shift & 1
            if position < EDGE_COUNT:
                mask |= bit << position
            elif bit:
                raise ValueError(f"nonzero graph6 padding: {record!r}")
            position += 1
    return mask


def encode_graph6(mask: int) -> str:
    if not 0 <= mask < LIMIT:
        raise ValueError("order-seven mask out of range")
    result = [chr(N + 63)]
    for start in range(0, EDGE_COUNT, 6):
        value = 0
        for offset in range(6):
            value <<= 1
            position = start + offset
            if position < EDGE_COUNT:
                value |= mask >> position & 1
        result.append(chr(value + 63))
    return "".join(result)


def read_records() -> tuple[str, ...]:
    digest = sha256(COVER_PATH)
    if digest != EXPECTED_COVER_SHA256:
        raise ValueError(f"cover5 SHA-256 mismatch: {digest}")
    records: list[str] = []
    for line_number, raw_line in enumerate(
        COVER_PATH.read_text(encoding="ascii").splitlines(), 1
    ):
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 2 or fields[0] != "7":
            raise ValueError(f"invalid cover5 row {line_number}: {raw_line!r}")
        records.append(fields[1])
    result = tuple(records)
    if result != EXPECTED_RECORDS:
        raise ValueError(f"cover5 records changed: {result}")
    return result


@functools.cache
def permutations() -> tuple[tuple[int, ...], ...]:
    return tuple(itertools.permutations(range(N)))


@functools.cache
def permutation_edge_maps() -> tuple[tuple[int, ...], ...]:
    return tuple(
        tuple(
            edge_position(permutation[left], permutation[right])
            for right in range(1, N)
            for left in range(right)
        )
        for permutation in permutations()
    )


def permute_bits(mask: int, edge_map: Sequence[int]) -> int:
    result = 0
    output = 1
    for source in edge_map:
        if mask >> source & 1:
            result |= output
        output <<= 1
    return result


def labelled_orbit(mask: int) -> frozenset[int]:
    return frozenset(permute_bits(mask, edge_map) for edge_map in permutation_edge_maps())


def permute_cube(cube: Cube, edge_map: Sequence[int]) -> Cube:
    ones, fixed = cube
    return permute_bits(ones, edge_map), permute_bits(fixed, edge_map)


def cube_orbit(cube: Cube) -> frozenset[Cube]:
    return frozenset(permute_cube(cube, edge_map) for edge_map in permutation_edge_maps())


@functools.cache
def clique_masks() -> tuple[int, ...]:
    return tuple(
        sum(
            1 << edge_position(left, right)
            for left, right in itertools.combinations(vertices, 2)
        )
        for vertices in itertools.combinations(range(N), 4)
    )


def r44_flags() -> bytearray:
    """Mark all 2^21 masks satisfying the 70 local R(4,4) clauses."""
    valid = bytearray(b"\x01") * LIMIT
    for clique in clique_masks():
        free = FULL ^ clique
        completion = free
        while True:
            valid[completion] = 0
            valid[clique | completion] = 0
            if completion == 0:
                break
            completion = (completion - 1) & free
    if sum(valid) != EXPECTED_R44:
        raise RuntimeError(f"local R(4,4) count changed: {sum(valid)}")
    return valid


def matching_assignments(cube: Cube) -> Iterable[int]:
    ones, fixed = cube
    if ones & ~fixed or fixed & ~FULL:
        raise ValueError(f"malformed cube: {cube}")
    free = FULL ^ fixed
    completion = free
    while True:
        yield ones | completion
        if completion == 0:
            break
        completion = (completion - 1) & free


def cube_is_safe(
    cube: Cube, valid: Sequence[int], forbidden: frozenset[int]
) -> bool:
    return all(not valid[mask] or mask in forbidden for mask in matching_assignments(cube))


def minimize_cube(
    mask: int, valid: Sequence[int], forbidden: frozenset[int]
) -> Cube:
    """Greedily remove edge literals in graph6 order; safety is monotone."""
    cube = (mask, FULL)
    for position in range(EDGE_COUNT):
        bit = 1 << position
        ones, fixed = cube
        candidate = (ones & ~bit, fixed & ~bit)
        if cube_is_safe(candidate, valid, forbidden):
            cube = candidate
    return cube


def complement_closure() -> dict[str, object]:
    raw_orbits = tuple(labelled_orbit(decode_graph6(record)) for record in read_records())
    raw = frozenset().union(*raw_orbits)
    complemented = frozenset(FULL ^ mask for mask in raw)
    closed = raw | complemented
    remaining = set(closed)
    class_orbits: dict[int, frozenset[int]] = {}
    while remaining:
        orbit = labelled_orbit(min(remaining))
        if not orbit <= closed:
            raise RuntimeError("complement closure is not S7-invariant")
        class_orbits[min(orbit)] = orbit
        remaining.difference_update(orbit)
    if len(raw) != EXPECTED_RAW_CLOSURE:
        raise RuntimeError(f"raw closure changed: {len(raw)}")
    if len(raw & complemented) != EXPECTED_COMPLEMENT_INTERSECTION:
        raise RuntimeError("raw/complement intersection changed")
    if len(closed) != EXPECTED_COMPLEMENT_CLOSURE:
        raise RuntimeError(f"complement closure changed: {len(closed)}")
    if len(class_orbits) != EXPECTED_ISOMORPHISM_CLASSES:
        raise RuntimeError(f"isomorphism-class count changed: {len(class_orbits)}")
    raw_orbit_sizes = tuple(map(len, raw_orbits))
    class_representatives = tuple(encode_graph6(mask) for mask in sorted(class_orbits))
    class_orbit_sizes = tuple(len(class_orbits[mask]) for mask in sorted(class_orbits))
    if raw_orbit_sizes != EXPECTED_RAW_ORBIT_SIZES:
        raise RuntimeError(f"raw orbit sizes changed: {raw_orbit_sizes}")
    if class_representatives != EXPECTED_CLASS_REPRESENTATIVES:
        raise RuntimeError(f"class representatives changed: {class_representatives}")
    if class_orbit_sizes != EXPECTED_CLASS_ORBIT_SIZES:
        raise RuntimeError(f"class orbit sizes changed: {class_orbit_sizes}")
    raw_hash = sha256_bytes(mask_bytes(raw))
    closed_hash = sha256_bytes(mask_bytes(closed))
    if raw_hash != EXPECTED_RAW_CLOSURE_SHA256:
        raise RuntimeError(f"raw closure SHA-256 changed: {raw_hash}")
    if closed_hash != EXPECTED_CLOSED_CLOSURE_SHA256:
        raise RuntimeError(f"closed closure SHA-256 changed: {closed_hash}")
    return {
        "raw_orbits": raw_orbits,
        "raw": raw,
        "complemented": complemented,
        "closed": closed,
        "class_orbits": class_orbits,
    }


def derive_cube_representatives(
    classes: dict[int, frozenset[int]],
    valid: Sequence[int],
    forbidden: frozenset[int],
) -> tuple[tuple[Cube, ...], tuple[Cube, ...]]:
    eight = tuple(
        min(
            (minimize_cube(labelled, valid, forbidden) for labelled in classes[canonical]),
            key=lambda cube: (cube[1].bit_count(), cube[1], cube[0]),
        )
        for canonical in sorted(classes)
    )
    unique_orbits: dict[Cube, frozenset[Cube]] = {}
    for cube in eight:
        orbit = cube_orbit(cube)
        unique_orbits.setdefault(min(orbit), orbit)
    six = tuple(
        sorted(
            unique_orbits,
            key=lambda cube: (cube[1].bit_count(), cube[1], cube[0]),
        )
    )
    if len(six) != EXPECTED_CUBE_ORBITS:
        raise RuntimeError(f"reduced cube-orbit count changed: {len(six)}")
    if eight != EXPECTED_INITIAL_CLASS_CUBES:
        raise RuntimeError(f"initial class cubes changed: {eight}")
    if six != CUBE_REPRESENTATIVES:
        raise RuntimeError(f"canonical cube representatives changed: {six}")
    return eight, six


def exact_cube_audit(
    representatives: Sequence[Cube],
    valid: Sequence[int],
    forbidden: frozenset[int],
) -> dict[str, object]:
    orbits = tuple(cube_orbit(cube) for cube in representatives)
    cubes = frozenset().union(*orbits)
    widths = Counter(fixed.bit_count() for _ones, fixed in cubes)
    if len(cubes) != EXPECTED_CUBES:
        raise RuntimeError(f"cube closure changed: {len(cubes)}")
    if dict(sorted(widths.items())) != EXPECTED_WIDTHS:
        raise RuntimeError(f"cube widths changed: {dict(widths)}")
    orbit_sizes = tuple(map(len, orbits))
    if orbit_sizes != EXPECTED_CUBE_ORBIT_SIZES:
        raise RuntimeError(f"cube orbit sizes changed: {orbit_sizes}")
    cube_hash = sha256_bytes(cube_bytes(cubes))
    if cube_hash != EXPECTED_CUBE_CLOSURE_SHA256:
        raise RuntimeError(f"cube closure SHA-256 changed: {cube_hash}")
    if {((fixed ^ ones), fixed) for ones, fixed in cubes} != cubes:
        raise RuntimeError("cube closure is not closed under complementation")

    coverage = array("I", [0]) * LIMIT
    orbit_coverage: list[set[int]] = []
    for orbit_index, orbit in enumerate(orbits):
        covered_by_orbit: set[int] = set()
        for cube in orbit:
            if not cube_is_safe(cube, valid, forbidden):
                raise RuntimeError(f"unsafe cube in orbit {orbit_index}: {cube}")
            for mask in matching_assignments(cube):
                if valid[mask]:
                    coverage[mask] += 1
                    covered_by_orbit.add(mask)
        orbit_coverage.append(covered_by_orbit)

    mismatches = 0
    for mask in range(LIMIT):
        expected = bool(valid[mask]) and mask in forbidden
        actual = coverage[mask] != 0
        mismatches += expected != actual
    if mismatches:
        raise RuntimeError(f"cube equivalence has {mismatches} mismatches")

    cubes_with_unique_witness = 0
    initially_removable = 0
    for cube in cubes:
        covered = tuple(mask for mask in matching_assignments(cube) if valid[mask])
        if any(coverage[mask] == 1 for mask in covered):
            cubes_with_unique_witness += 1
        else:
            initially_removable += 1

    orbit_removal_misses = []
    for removed in range(len(orbits)):
        covered_elsewhere = set().union(
            *(
                coverage_set
                for index, coverage_set in enumerate(orbit_coverage)
                if index != removed
            )
        )
        orbit_removal_misses.append(len(forbidden - covered_elsewhere))
    if cubes_with_unique_witness != EXPECTED_CUBES or initially_removable != 0:
        raise RuntimeError("the frozen cube family is no longer deletion-irredundant")
    if tuple(orbit_removal_misses) != EXPECTED_ORBIT_REMOVAL_MISSES:
        raise RuntimeError(f"orbit removal witnesses changed: {orbit_removal_misses}")

    return {
        "orbits": orbits,
        "cubes": cubes,
        "widths": dict(sorted(widths.items())),
        "coverage": coverage,
        "cubes_with_unique_witness": cubes_with_unique_witness,
        "initially_removable_cubes": initially_removable,
        "orbit_removal_misses": tuple(orbit_removal_misses),
    }


def mask_bytes(masks: Iterable[int]) -> bytes:
    return "".join(f"{mask:06X}\n" for mask in sorted(masks)).encode("ascii")


def cube_bytes(cubes: Iterable[Cube]) -> bytes:
    return "".join(
        f"{ones:06X}\t{fixed:06X}\n"
        for ones, fixed in sorted(cubes, key=lambda cube: (cube[1], cube[0]))
    ).encode("ascii")


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def audit() -> dict[str, object]:
    closure = complement_closure()
    valid = r44_flags()
    eight, six = derive_cube_representatives(
        closure["class_orbits"], valid, closure["closed"]
    )
    exact = exact_cube_audit(six, valid, closure["closed"])
    raw_orbits = closure["raw_orbits"]
    class_orbits = closure["class_orbits"]
    cube_orbits = exact["orbits"]
    return {
        "schema_version": 1,
        "status": "PASS",
        "scope": {
            "self_complementary_local_target": True,
            "checked_assignments": LIMIT,
            "k12_formula_generated": False,
            "solver_invoked": False,
            "unsat_claimed": False,
            "six_orbit_global_minimality_claimed": False,
        },
        "source": {
            "path": str(COVER_PATH),
            "sha256": sha256(COVER_PATH),
            "records": list(read_records()),
        },
        "complement_closure": {
            "raw_orbit_sizes": [len(orbit) for orbit in raw_orbits],
            "raw_labelled_masks": len(closure["raw"]),
            "complemented_labelled_masks": len(closure["complemented"]),
            "raw_complement_intersection": len(
                closure["raw"] & closure["complemented"]
            ),
            "closed_labelled_masks": len(closure["closed"]),
            "raw_closure_sha256": sha256_bytes(mask_bytes(closure["raw"])),
            "closed_closure_sha256": sha256_bytes(mask_bytes(closure["closed"])),
            "unique_isomorphism_classes": len(class_orbits),
            "class_representatives_graph6": [
                encode_graph6(mask) for mask in sorted(class_orbits)
            ],
            "class_orbit_sizes": [len(class_orbits[mask]) for mask in sorted(class_orbits)],
        },
        "cube_reduction": {
            "initial_class_cubes": [
                {"ones": f"0x{ones:X}", "fixed": f"0x{fixed:X}", "width": fixed.bit_count()}
                for ones, fixed in eight
            ],
            "unique_s7_representatives": [
                {"ones": f"0x{ones:X}", "fixed": f"0x{fixed:X}", "width": fixed.bit_count()}
                for ones, fixed in six
            ],
            "representative_count": len(six),
            "orbit_sizes": [len(orbit) for orbit in cube_orbits],
            "unique_cubes": len(exact["cubes"]),
            "widths": exact["widths"],
            "cube_closure_sha256": sha256_bytes(cube_bytes(exact["cubes"])),
            "exact_on_local_r44": True,
        },
        "reduction_search": {
            "cubes_with_unique_witness": exact["cubes_with_unique_witness"],
            "initially_removable_cubes": exact["initially_removable_cubes"],
            "orbit_removal_misses": list(exact["orbit_removal_misses"]),
            "symmetry_preserving_orbit_removal_possible": any(
                misses == 0 for misses in exact["orbit_removal_misses"]
            ),
            "individual_cube_deletion_possible": exact["initially_removable_cubes"] > 0,
            "frozen_family_deletion_irredundant": (
                exact["cubes_with_unique_witness"] == EXPECTED_CUBES
            ),
            "alternative_cube_families_searched": False,
            "global_minimality_conclusion": False,
        },
        "exhaustive_check": {
            "assignments": LIMIT,
            "r44_assignments": sum(valid),
            "forbidden_r44_assignments": len(closure["closed"]),
            "rejected_r44_assignments": sum(
                bool(valid[mask]) and exact["coverage"][mask] != 0
                for mask in range(LIMIT)
            ),
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("audit", nargs="?")
    parser.parse_args()
    print(json.dumps(audit(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
