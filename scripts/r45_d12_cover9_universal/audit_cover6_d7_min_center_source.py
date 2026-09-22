#!/usr/bin/env python3
"""Bounded standalone audit of the normalized cover6 degree-seven source.

The audited CNF is the deterministic degree-seven source ``F7`` followed by
nine clauses encoding the minimum-centre normalization

    p in {1, 2}, q in {0, ..., 4}, p + q >= 2,

where ``p`` counts neighbours of vertex 1 in vertices 2..7 and ``q`` counts
neighbours in vertices 8..11.  The program reconstructs the six frozen S7
cube orbits, both conditioned catalogue families, their compact cube/witness
payloads, and the ordered 4,312,419-clause F7 body from primitive constants.
It hashes the F7 and F7-plus-nine DIMACS streams without writing either CNF.

This file deliberately imports no project generator, solver, LRAT checker, or
Lean module.  It only reads the six-record cover TSV and the tracked d8
conditioned-witness report used for byte-for-byte payload reuse comparisons.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import itertools
import json
import math
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable, Iterator, Sequence


LOCAL_ORDER = 7
LOCAL_EDGES = 21
LOCAL_FULL = (1 << LOCAL_EDGES) - 1
GLOBAL_ORDER = 12
GLOBAL_VARIABLES = 66
ROOT_DEGREE = 7

HERE = Path(__file__).resolve().parent
COVER_TSV = (
    HERE.parent
    / "r45_d12_complement_closed_minimum"
    / "cover6_complement_closed.tsv"
)
D8_WITNESS_REPORT = HERE / "COVER6_CONDITIONED_ORBIT_WITNESSES_V1.json"
D7_NEW_CUBE_PAYLOAD = HERE / "COVER6_D7_NEW_CUBE_PAYLOAD_V1.bin"

COVER_TSV_SHA256 = (
    "404E49E3218424FCB73314ADEE42CC873CD3F8D67E4615653A8BC0210F61AD16"
)
COVER_RECORDS = ("F@h^g", "FKDhw", "FG`Xo", "FdW}w", "FHFLw", "FIIXw")
COVER_ORBIT_SIZES = (5_040, 5_040, 2_520, 2_520, 5_040, 5_040)
LABELLED_MASK_COUNT = 25_200
LABELLED_MASK_SHA256 = (
    "04B9688924BFC2EF6F92FB5734B19E7E771C37446DD3E442ECED8648BE1CBDD7"
)

CUBE_REPRESENTATIVES = (
    (0x3, 0xDF677),
    (0x3E6BE, 0x1BE6BE),
    (0x84AE, 0x18FDFE),
    (0x8CF5, 0x1B8FFD),
    (0x897E, 0x15FDFE),
    (0x84ED, 0x1DF5EF),
)
CUBE_ORBIT_SIZES = (2_520, 2_520, 5_040, 5_040, 5_040, 5_040)
CUBE_COUNT = 25_200
CUBE_WIDTHS = {15: 5_040, 16: 10_080, 17: 10_080}
CUBE_SHA256 = (
    "0239E74AC009B28173E59C3293F7F9C9370A99832B19BB28205EF449E6238F7D"
)

BLOCK_COUNTS = (2_520, 4_680, 10_200, 15_480, 15_480, 10_200, 4_680, 2_520)
LOCAL_COUNTS = (0, 300, 360, 540, 360, 300, 0)
BASE_CLAUSES = 699
ROOT_FREE_K7_CLAUSES = 4_127_760
ROOT_CONTAINING_K6_CLAUSES = 183_960
F7_CLAUSES = 4_312_419

# Variables 12..17 are (1,2)..(1,7); 18..21 are (1,8)..(1,11).
# The order is part of the audited byte stream: all nine clauses follow F7.
EXTRA_CLAUSES: tuple[tuple[int, ...], ...] = (
    (12,),
    (-14,),
    (14, -15),
    (15, -16),
    (16, -17),
    (18, -19),
    (19, -20),
    (20, -21),
    (13, 18),
)
MASTER7_CLAUSES = F7_CLAUSES + len(EXTRA_CLAUSES)
EXPECTED_PAIRS = tuple(
    [(1, q) for q in range(1, 5)] + [(2, q) for q in range(5)]
)

# Frozen after the standalone stream was reproduced byte-for-byte through the
# older production generator's independently implemented catalogue/stream path.
EXPECTED_F7_BYTES: int | None = 246_507_515
EXPECTED_F7_SHA256: str | None = (
    "85A93BEEA81BC890E3343A5A52094380446432F81AF9B28A2A35F9B76CAC920C"
)
EXPECTED_MASTER7_BYTES: int | None = 246_507_588
EXPECTED_MASTER7_SHA256: str | None = (
    "DFA3F7C3C1ADF2F6C8855FA5F08D11D54BFC826205246E68DAD5F4F5D46A5BBE"
)

ALPHABET = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz-_"
WITNESS_BITS = 15
CUBE_DIGITS = 7
PERMUTATION_COUNT = math.factorial(LOCAL_ORDER)

Cube = tuple[int, int]
Clause = tuple[int, ...]
Witness = tuple[int, int]


class D7AuditError(ValueError):
    """Raised at the first exactness, convention, or fingerprint mismatch."""


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def local_edge(left: int, right: int) -> int:
    if left > right:
        left, right = right, left
    if not 0 <= left < right < LOCAL_ORDER:
        raise ValueError("not an edge of the local K7")
    return right * (right - 1) // 2 + left


def global_edge(left: int, right: int) -> int:
    if left > right:
        left, right = right, left
    if not 0 <= left < right < GLOBAL_ORDER:
        raise ValueError("not an edge of K12")
    return left * (2 * GLOBAL_ORDER - left - 1) // 2 + right - left


def decode_graph6(record: str) -> int:
    if len(record) != 5 or ord(record[0]) != LOCAL_ORDER + 63:
        raise D7AuditError(f"invalid order-seven graph6 record: {record!r}")
    bits: list[int] = []
    for character in record[1:]:
        value = ord(character) - 63
        if not 0 <= value < 64:
            raise D7AuditError(f"invalid graph6 payload: {record!r}")
        bits.extend((value >> shift) & 1 for shift in range(5, -1, -1))
    if any(bits[LOCAL_EDGES:]):
        raise D7AuditError(f"nonzero graph6 padding: {record!r}")
    return sum(bit << position for position, bit in enumerate(bits[:LOCAL_EDGES]))


def read_cover_records() -> tuple[str, ...]:
    digest = file_sha256(COVER_TSV)
    if digest != COVER_TSV_SHA256:
        raise D7AuditError(f"cover TSV SHA-256 mismatch: {digest}")
    records = []
    for line_number, raw in enumerate(
        COVER_TSV.read_text(encoding="ascii").splitlines(), 1
    ):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 2 or fields[0] != "7":
            raise D7AuditError(f"malformed cover TSV row {line_number}")
        records.append(fields[1])
    result = tuple(records)
    if result != COVER_RECORDS:
        raise D7AuditError(f"cover records changed: {result}")
    return result


@functools.cache
def permutation_maps() -> tuple[tuple[int, ...], ...]:
    result = tuple(
        tuple(
            local_edge(permutation[left], permutation[right])
            for right in range(1, LOCAL_ORDER)
            for left in range(right)
        )
        for permutation in itertools.permutations(range(LOCAL_ORDER))
    )
    if len(result) != PERMUTATION_COUNT:
        raise D7AuditError("S7 enumeration changed")
    return result


def transform(mask: int, mapping: Sequence[int]) -> int:
    return sum(
        ((mask >> source) & 1) << target
        for target, source in enumerate(mapping)
    )


def graph_orbit(mask: int) -> frozenset[int]:
    return frozenset(transform(mask, mapping) for mapping in permutation_maps())


def cube_orbit(cube: Cube) -> frozenset[Cube]:
    ones, fixed = cube
    return frozenset(
        (transform(ones, mapping), transform(fixed, mapping))
        for mapping in permutation_maps()
    )


def masks_digest(masks: Iterable[int]) -> str:
    return sha256_bytes(
        "".join(f"{mask:06X}\n" for mask in sorted(masks)).encode("ascii")
    )


def cubes_digest(cubes: Iterable[Cube]) -> str:
    return sha256_bytes(
        "".join(
            f"{ones:06X}\t{fixed:06X}\n"
            for ones, fixed in sorted(cubes, key=lambda cube: (cube[1], cube[0]))
        ).encode("ascii")
    )


@functools.cache
def forbidden_masks() -> frozenset[int]:
    pieces = tuple(graph_orbit(decode_graph6(record)) for record in read_cover_records())
    if tuple(map(len, pieces)) != COVER_ORBIT_SIZES:
        raise D7AuditError("cover orbit sizes changed")
    if any(
        pieces[left] & pieces[right]
        for left in range(len(pieces))
        for right in range(left)
    ):
        raise D7AuditError("cover motif orbits overlap")
    result = frozenset().union(*pieces)
    if len(result) != LABELLED_MASK_COUNT:
        raise D7AuditError("cover labelled-mask count changed")
    if masks_digest(result) != LABELLED_MASK_SHA256:
        raise D7AuditError("cover labelled-mask digest changed")
    if {LOCAL_FULL ^ mask for mask in result} != result:
        raise D7AuditError("cover target is not complement-closed")
    return result


@functools.cache
def reduced_cubes() -> tuple[Cube, ...]:
    pieces = tuple(cube_orbit(cube) for cube in CUBE_REPRESENTATIVES)
    if tuple(map(len, pieces)) != CUBE_ORBIT_SIZES:
        raise D7AuditError("cube orbit sizes changed")
    if any(
        pieces[left] & pieces[right]
        for left in range(len(pieces))
        for right in range(left)
    ):
        raise D7AuditError("cube representative orbits overlap")
    result = frozenset().union(*pieces)
    if len(result) != CUBE_COUNT:
        raise D7AuditError("cube closure size changed")
    if any(ones & ~fixed or fixed & ~LOCAL_FULL for ones, fixed in result):
        raise D7AuditError("malformed cube")
    if {(fixed ^ ones, fixed) for ones, fixed in result} != result:
        raise D7AuditError("cube family is not complement-closed")
    widths = Counter(fixed.bit_count() for _ones, fixed in result)
    if dict(sorted(widths.items())) != CUBE_WIDTHS:
        raise D7AuditError("cube width distribution changed")
    if cubes_digest(result) != CUBE_SHA256:
        raise D7AuditError("cube closure digest changed")
    return tuple(
        sorted(result, key=lambda cube: (cube[1].bit_count(), cube[1], cube[0]))
    )


def completions(cube: Cube) -> Iterator[int]:
    ones, fixed = cube
    remaining = LOCAL_FULL ^ fixed
    while True:
        yield ones | remaining
        if remaining == 0:
            break
        remaining = (remaining - 1) & (LOCAL_FULL ^ fixed)


@functools.cache
def four_cliques() -> tuple[int, ...]:
    return tuple(
        sum(
            1 << local_edge(left, right)
            for left, right in itertools.combinations(vertices, 2)
        )
        for vertices in itertools.combinations(range(LOCAL_ORDER), 4)
    )


def is_r44(mask: int) -> bool:
    return all((mask & clique) not in (0, clique) for clique in four_cliques())


def validate_local_cube_exactness() -> dict[str, int | bool]:
    target = forbidden_masks()
    if any(not is_r44(mask) for mask in target):
        raise D7AuditError("a cover motif is not locally R(4,4)-free")
    covered: set[int] = set()
    checked_completions = 0
    for cube in reduced_cubes():
        for mask in completions(cube):
            checked_completions += 1
            if not is_r44(mask):
                continue
            if mask not in target:
                raise D7AuditError(f"cube rejects an allowed R(4,4) mask {mask:#x}")
            covered.add(mask)
    if covered != target:
        raise D7AuditError(f"cube closure misses {len(target - covered)} cover masks")
    return {
        "cube_completions_checked": checked_completions,
        "forbidden_r44_masks": len(target),
        "covered_forbidden_masks": len(covered),
        "exact_on_local_r44": True,
    }


def triangle_masks(vertices: range) -> tuple[int, ...]:
    return tuple(
        sum(
            1 << local_edge(left, right)
            for left, right in itertools.combinations(triple, 2)
        )
        for triple in itertools.combinations(vertices, 3)
    )


def block_forbidden_masks(neighbour_count: int) -> tuple[int, ...]:
    if not 0 <= neighbour_count <= LOCAL_ORDER:
        raise ValueError("block neighbour count must be in 0..7")
    positive = triangle_masks(range(neighbour_count))
    negative = triangle_masks(range(neighbour_count, LOCAL_ORDER))
    return tuple(
        sorted(
            mask
            for mask in forbidden_masks()
            if all((mask & triangle) != triangle for triangle in positive)
            and all((mask & triangle) != 0 for triangle in negative)
        )
    )


@functools.cache
def block_catalogues() -> tuple[tuple[Cube, ...], ...]:
    result = []
    for neighbour_count in range(LOCAL_ORDER + 1):
        target = block_forbidden_masks(neighbour_count)
        index = {mask: item for item, mask in enumerate(target)}
        by_coverage: dict[frozenset[int], Cube] = {}
        for ones, fixed in reduced_cubes():
            coverage = frozenset(
                item
                for mask in completions((ones, fixed))
                if (item := index.get(mask)) is not None
            )
            if not coverage:
                continue
            previous = by_coverage.get(coverage)
            if previous is None or (fixed.bit_count(), fixed, ones) < (
                previous[1].bit_count(),
                previous[1],
                previous[0],
            ):
                by_coverage[coverage] = (ones, fixed)
        union = frozenset().union(*by_coverage) if by_coverage else frozenset()
        if union != frozenset(range(len(target))):
            raise D7AuditError(f"block catalogue misses a={neighbour_count}")
        selected = tuple(
            sorted(
                by_coverage.values(),
                key=lambda cube: (cube[1].bit_count(), cube[1], cube[0]),
            )
        )
        result.append(selected)
    observed = tuple(map(len, result))
    if observed != BLOCK_COUNTS:
        raise D7AuditError(f"block catalogue counts changed: {observed}")
    return tuple(result)


def project_nonroot(mask: int) -> int:
    result = 0
    for right in range(2, LOCAL_ORDER):
        for left in range(1, right):
            if (mask >> local_edge(left, right)) & 1:
                result |= 1 << local_edge(left - 1, right - 1)
    return result


@functools.cache
def local_catalogues() -> tuple[tuple[Cube, ...], ...]:
    root_positions = tuple(local_edge(0, vertex) for vertex in range(1, 7))
    result = []
    for neighbour_count in range(7):
        target = tuple(
            sorted(
                {
                    project_nonroot(mask)
                    for mask in forbidden_masks()
                    if all(
                        bool((mask >> position) & 1) == (vertex <= neighbour_count)
                        for vertex, position in enumerate(root_positions, 1)
                    )
                }
            )
        )
        index = {mask: item for item, mask in enumerate(target)}
        projected_cubes: set[Cube] = set()
        for ones, fixed in reduced_cubes():
            if all(
                not ((fixed >> position) & 1)
                or bool((ones >> position) & 1) == (vertex <= neighbour_count)
                for vertex, position in enumerate(root_positions, 1)
            ):
                projected_cubes.add((project_nonroot(ones), project_nonroot(fixed)))
        candidates = []
        for ones, fixed in projected_cubes:
            coverage = frozenset(
                index[mask] for mask in target if (mask & fixed) == ones
            )
            if coverage:
                candidates.append((coverage, ones, fixed))
        active = set(range(len(target)))
        selected: list[Cube] = []
        while active:
            coverage, ones, fixed = max(
                candidates,
                key=lambda item: (
                    len(active & item[0]),
                    -item[2].bit_count(),
                    -item[2],
                    -item[1],
                ),
            )
            newly_covered = active & coverage
            if not newly_covered:
                raise D7AuditError(f"local catalogue greedy cover stuck at a={neighbour_count}")
            selected.append((ones, fixed))
            active -= newly_covered
        ordered = tuple(
            sorted(
                set(selected),
                key=lambda cube: (cube[1].bit_count(), cube[1], cube[0]),
            )
        )
        rejected = {
            mask
            for mask in target
            if any((mask & fixed) == ones for ones, fixed in ordered)
        }
        if rejected != set(target):
            raise D7AuditError(f"local catalogue misses a={neighbour_count}")
        result.append(ordered)
    observed = tuple(map(len, result))
    if observed != LOCAL_COUNTS:
        raise D7AuditError(f"local catalogue counts changed: {observed}")
    return tuple(result)


def encode_base64_le(value: int, digits: int) -> str:
    if value < 0 or value >= 1 << (6 * digits):
        raise D7AuditError(f"value {value} does not fit in {digits} digits")
    return "".join(ALPHABET[(value >> (6 * digit)) & 63] for digit in range(digits))


def encode_cube(cube: Cube) -> str:
    ones, fixed = cube
    if ones & ~fixed or fixed & ~LOCAL_FULL:
        raise D7AuditError(f"malformed cube payload input: {cube!r}")
    return encode_base64_le(ones + (fixed << LOCAL_EDGES), CUBE_DIGITS)


def cube_payload(cubes: Sequence[Cube]) -> str:
    return "".join(encode_cube(cube) for cube in cubes)


def decoded_payload_fingerprint(cubes: Sequence[Cube]) -> int:
    """Match Lean's 64-bit FNV-style fingerprint over packed cube words."""
    result = 14_695_981_039_346_656_037
    for ones, fixed in cubes:
        result ^= ones + (fixed << LOCAL_EDGES)
        result = result * 1_099_511_628_211 % (1 << 64)
    return result


@functools.cache
def orbit_witness_index() -> dict[Cube, Witness]:
    result: dict[Cube, Witness] = {}
    owners: dict[Cube, int] = {}
    for representative_index, representative in enumerate(CUBE_REPRESENTATIVES):
        for permutation_index, mapping in enumerate(permutation_maps()):
            transformed = (
                transform(representative[0], mapping),
                transform(representative[1], mapping),
            )
            previous = owners.get(transformed)
            if previous is not None and previous != representative_index:
                raise D7AuditError("cube representative witness orbits overlap")
            owners[transformed] = representative_index
            result.setdefault(transformed, (representative_index, permutation_index))
    if set(result) != set(reduced_cubes()):
        raise D7AuditError("orbit witness index differs from cube closure")
    return result


def pack_witnesses(witnesses: Sequence[Witness]) -> str:
    accumulator = 0
    available = 0
    output = []
    for representative_index, permutation_index in witnesses:
        if not 0 <= representative_index < len(CUBE_REPRESENTATIVES):
            raise D7AuditError("representative index out of range")
        if not 0 <= permutation_index < PERMUTATION_COUNT:
            raise D7AuditError("permutation rank out of range")
        code = representative_index + len(CUBE_REPRESENTATIVES) * permutation_index
        if code >= 1 << WITNESS_BITS:
            raise D7AuditError("witness code does not fit in fifteen bits")
        accumulator |= code << available
        available += WITNESS_BITS
        while available >= 6:
            output.append(ALPHABET[accumulator & 63])
            accumulator >>= 6
            available -= 6
    if available:
        output.append(ALPHABET[accumulator & 63])
    expected = (len(witnesses) * WITNESS_BITS + 5) // 6
    if len(output) != expected:
        raise D7AuditError("packed witness length arithmetic changed")
    return "".join(output)


def compatible_with_root(cube: Cube, neighbour_count: int) -> bool:
    ones, fixed = cube
    return all(
        not ((fixed >> local_edge(0, vertex)) & 1)
        or bool((ones >> local_edge(0, vertex)) & 1) == (vertex <= neighbour_count)
        for vertex in range(1, 7)
    )


def canonical_local_lifts(
    neighbour_count: int, selected: Sequence[Cube]
) -> tuple[tuple[Cube, int], ...]:
    lifts: dict[Cube, list[Cube]] = defaultdict(list)
    for cube in reduced_cubes():
        if compatible_with_root(cube, neighbour_count):
            projected = project_nonroot(cube[0]), project_nonroot(cube[1])
            lifts[projected].append(cube)
    result = []
    for projected in selected:
        candidates = tuple(
            sorted(lifts.get(projected, ()), key=lambda cube: (cube[1], cube[0]))
        )
        if not candidates:
            raise D7AuditError(
                f"projected cube lacks a full lift at a={neighbour_count}"
            )
        result.append((candidates[0], len(candidates)))
    return tuple(result)


def section_report(
    neighbour_count: int,
    cubes: Sequence[Cube],
    *,
    kind: str,
) -> tuple[dict[str, object], str, str]:
    packed_cubes = cube_payload(cubes)
    witnesses = orbit_witness_index()
    multiplicities: Counter[int] | None = None
    if kind == "full_k7":
        rows = tuple(witnesses[cube] for cube in cubes)
        semantic_key = "cube_sha256"
    elif kind == "projected_k6":
        lifts = canonical_local_lifts(neighbour_count, cubes)
        rows = tuple(witnesses[lift] for lift, _multiplicity in lifts)
        multiplicities = Counter(multiplicity for _lift, multiplicity in lifts)
        semantic_key = "projected_cube_sha256"
    else:
        raise ValueError(f"unknown section kind: {kind}")
    packed_witnesses = pack_witnesses(rows)
    report: dict[str, object] = {
        "neighbour_count": neighbour_count,
        "entries": len(cubes),
        semantic_key: cubes_digest(cubes),
        "packed_cube_ascii_characters": len(packed_cubes),
        "packed_cube_sha256": sha256_bytes(packed_cubes.encode("ascii")),
        "packed_witness_ascii_characters": len(packed_witnesses),
        "packed_witness_sha256": sha256_bytes(packed_witnesses.encode("ascii")),
        "representative_counts": {
            str(index): count
            for index, count in sorted(Counter(row[0] for row in rows).items())
        },
        "minimum_permutation_rank": min((row[1] for row in rows), default=None),
        "maximum_permutation_rank": max((row[1] for row in rows), default=None),
    }
    if multiplicities is not None:
        report["full_lift_multiplicity_counts"] = {
            str(value): count for value, count in sorted(multiplicities.items())
        }
    return report, packed_cubes, packed_witnesses


def read_d8_report() -> tuple[dict[str, object], str]:
    if not D8_WITNESS_REPORT.is_file():
        raise D7AuditError(f"missing tracked d8 witness report: {D8_WITNESS_REPORT}")
    digest = file_sha256(D8_WITNESS_REPORT)
    report = json.loads(D8_WITNESS_REPORT.read_text(encoding="utf-8"))
    if report.get("status") != "PASS_EXACT_CONDITIONED_ORBIT_WITNESSES":
        raise D7AuditError("tracked d8 witness report status changed")
    return report, digest


def payload_audit() -> dict[str, object]:
    blocks = block_catalogues()
    locals_ = local_catalogues()
    d8, d8_file_digest = read_d8_report()

    block_rows = []
    block_cube_payloads: dict[int, str] = {}
    block_witness_payloads: dict[int, str] = {}
    d8_block_sections = {
        int(row["root_neighbours_in_seven_set"]): row
        for row in d8["full_k7_orbit_witnesses"]["sections"]
    }
    for count in range(3, 8):
        row, cube_data, witness_data = section_report(
            count, blocks[count], kind="full_k7"
        )
        row["d7_role"] = "new" if count == 3 else "reused_byte_for_byte_from_d8"
        if count >= 4:
            expected = d8_block_sections[count]
            if row["cube_sha256"] != expected["cube_sha256"]:
                raise D7AuditError(f"d8 K7 semantic section changed at a={count}")
            if row["packed_witness_sha256"] != expected["witness_sha256"]:
                raise D7AuditError(f"d8 K7 witness section changed at a={count}")
        block_rows.append(row)
        block_cube_payloads[count] = cube_data
        block_witness_payloads[count] = witness_data

    local_rows = []
    local_cube_payloads: dict[int, str] = {}
    local_witness_payloads: dict[int, str] = {}
    d8_local_sections = {
        int(row["root_neighbours_among_six_vertices"]): row
        for row in d8["projected_k6_canonical_lift_orbit_witnesses"]["sections"]
    }
    for count in range(2, 6):
        row, cube_data, witness_data = section_report(
            count, locals_[count], kind="projected_k6"
        )
        row["d7_role"] = "new" if count == 2 else "reused_byte_for_byte_from_d8"
        if count >= 3:
            expected = d8_local_sections[count]
            if row["projected_cube_sha256"] != expected["projected_cube_sha256"]:
                raise D7AuditError(f"d8 K6 semantic section changed at a={count}")
            if row["packed_witness_sha256"] != expected["witness_sha256"]:
                raise D7AuditError(f"d8 K6 witness section changed at a={count}")
        local_rows.append(row)
        local_cube_payloads[count] = cube_data
        local_witness_payloads[count] = witness_data

    reused_block_cubes = "".join(block_cube_payloads[count] for count in range(4, 8))
    reused_block_witnesses = "".join(
        block_witness_payloads[count] for count in range(4, 8)
    )
    reused_local_cubes = "".join(local_cube_payloads[count] for count in range(3, 6))
    reused_local_witnesses = "".join(
        local_witness_payloads[count] for count in range(3, 6)
    )
    d8_block_source = d8["source_payloads"]["full_k7_conditioned_cubes"]
    d8_local_source = d8["source_payloads"]["projected_k6_conditioned_cubes"]
    comparisons = {
        "k7_a4_through_a7_cube_payload": (
            sha256_bytes(reused_block_cubes.encode("ascii"))
            == d8_block_source["sha256"]
        ),
        "k7_a4_through_a7_witness_payload": (
            sha256_bytes(reused_block_witnesses.encode("ascii"))
            == d8["full_k7_orbit_witnesses"]["sha256"]
        ),
        "k6_a3_through_a5_cube_payload": (
            sha256_bytes(reused_local_cubes.encode("ascii"))
            == d8_local_source["sha256"]
        ),
        "k6_a3_through_a5_witness_payload": (
            sha256_bytes(reused_local_witnesses.encode("ascii"))
            == d8["projected_k6_canonical_lift_orbit_witnesses"]["sha256"]
        ),
    }
    if not all(comparisons.values()):
        raise D7AuditError(f"d8 payload suffix reuse failed: {comparisons}")

    full_block_cubes = "".join(block_cube_payloads[count] for count in range(3, 8))
    full_block_witnesses = "".join(
        block_witness_payloads[count] for count in range(3, 8)
    )
    full_local_cubes = "".join(local_cube_payloads[count] for count in range(2, 6))
    full_local_witnesses = "".join(
        local_witness_payloads[count] for count in range(2, 6)
    )
    return {
        "status": "PASS",
        "tracked_d8_report": {
            "name": D8_WITNESS_REPORT.name,
            "sha256": d8_file_digest,
        },
        "reuse_checks": comparisons,
        "full_k7": {
            "neighbour_counts": list(range(3, 8)),
            "section_entries": [len(blocks[count]) for count in range(3, 8)],
            "entries": sum(len(blocks[count]) for count in range(3, 8)),
            "packed_cube_ascii_characters": len(full_block_cubes),
            "packed_cube_sha256": sha256_bytes(full_block_cubes.encode("ascii")),
            "packed_witness_ascii_characters": len(full_block_witnesses),
            "packed_witness_sha256": sha256_bytes(
                full_block_witnesses.encode("ascii")
            ),
            "sections": block_rows,
        },
        "projected_k6": {
            "neighbour_counts": list(range(2, 6)),
            "section_entries": [len(locals_[count]) for count in range(2, 6)],
            "entries": sum(len(locals_[count]) for count in range(2, 6)),
            "packed_cube_ascii_characters": len(full_local_cubes),
            "packed_cube_sha256": sha256_bytes(full_local_cubes.encode("ascii")),
            "packed_witness_ascii_characters": len(full_local_witnesses),
            "packed_witness_sha256": sha256_bytes(
                full_local_witnesses.encode("ascii")
            ),
            "sections": local_rows,
        },
    }


def emit_lean_payload() -> dict[str, object]:
    """Write only the two D7-only cube sections needed beside Master8.

    The byte stream is the seven-character little-endian cube encoding for
    K7/a=3 followed immediately by K6/a=2.  It contains no newline or other
    platform-sensitive separator; the two frozen byte lengths are the format.
    """
    blocks = block_catalogues()
    locals_ = local_catalogues()
    block_payload = cube_payload(blocks[3]).encode("ascii")
    local_payload = cube_payload(locals_[2]).encode("ascii")
    payload = block_payload + local_payload
    D7_NEW_CUBE_PAYLOAD.write_bytes(payload)
    return {
        "status": "PASS_WROTE_D7_NEW_CUBE_PAYLOAD",
        "path": D7_NEW_CUBE_PAYLOAD.name,
        "format": "raw ASCII base64le cube words; K7/a=3 then K6/a=2; no separator or newline",
        "bytes": len(payload),
        "sha256": sha256_bytes(payload),
        "sections": {
            "full_k7_a3": {
                "offset": 0,
                "entries": len(blocks[3]),
                "bytes": len(block_payload),
                "sha256": sha256_bytes(block_payload),
                "decoded_fnv64": decoded_payload_fingerprint(blocks[3]),
            },
            "projected_k6_a2": {
                "offset": len(block_payload),
                "entries": len(locals_[2]),
                "bytes": len(local_payload),
                "sha256": sha256_bytes(local_payload),
                "decoded_fnv64": decoded_payload_fingerprint(locals_[2]),
            },
        },
        "inputs": {
            "cover_tsv": COVER_TSV.name,
            "cover_tsv_sha256": file_sha256(COVER_TSV),
            "tracked_d8_report": D8_WITNESS_REPORT.name,
            "tracked_d8_report_sha256": file_sha256(D8_WITNESS_REPORT),
        },
    }


def base_clauses() -> tuple[Clause, ...]:
    clauses: list[Clause] = []
    for vertices in itertools.combinations(range(1, GLOBAL_ORDER), 4):
        edges = tuple(
            global_edge(left, right)
            for left, right in itertools.combinations(vertices, 2)
        )
        clauses.append(tuple(-edge for edge in edges))
        clauses.append(edges)
    for vertices in itertools.combinations(range(1, ROOT_DEGREE + 1), 3):
        clauses.append(
            tuple(
                -global_edge(left, right)
                for left, right in itertools.combinations(vertices, 2)
            )
        )
    for vertices in itertools.combinations(range(ROOT_DEGREE + 1, 12), 3):
        clauses.append(
            tuple(
                global_edge(left, right)
                for left, right in itertools.combinations(vertices, 2)
            )
        )
    result = tuple(clauses)
    if len(result) != BASE_CLAUSES:
        raise D7AuditError(f"degree-seven base count changed: {len(result)}")
    if any(abs(literal) <= 11 for clause in result for literal in clause):
        raise D7AuditError("root variable survives the degree-seven base")
    return result


def subset_variables(vertices: Sequence[int]) -> tuple[int, ...]:
    if tuple(vertices) != tuple(sorted(vertices)):
        raise ValueError("subset vertices must be increasing")
    return tuple(
        global_edge(vertices[left], vertices[right])
        for right in range(1, len(vertices))
        for left in range(right)
    )


def compiled_cube(cube: Cube, positions: int) -> tuple[tuple[int, bool], ...]:
    ones, fixed = cube
    return tuple(
        (position, bool((ones >> position) & 1))
        for position in range(positions)
        if (fixed >> position) & 1
    )


def clause_line(clause: Sequence[int]) -> bytes:
    if not clause:
        return b"0\n"
    return (" ".join(map(str, clause)) + " 0\n").encode("ascii")


def arithmetic_counts() -> dict[str, int]:
    base = 2 * math.comb(11, 4) + math.comb(7, 3) + math.comb(4, 3)
    root_free = sum(
        math.comb(7, neighbours)
        * math.comb(4, 7 - neighbours)
        * BLOCK_COUNTS[neighbours]
        for neighbours in range(8)
        if neighbours <= 7 and 7 - neighbours <= 4
    )
    root_containing = sum(
        math.comb(7, neighbours)
        * math.comb(4, 6 - neighbours)
        * LOCAL_COUNTS[neighbours]
        for neighbours in range(7)
        if neighbours <= 7 and 6 - neighbours <= 4
    )
    result = {
        "base": base,
        "root_free_k7": root_free,
        "root_containing_k6": root_containing,
        "f7": base + root_free + root_containing,
        "normalization_extras": len(EXTRA_CLAUSES),
        "master7": base + root_free + root_containing + len(EXTRA_CLAUSES),
    }
    expected = {
        "base": BASE_CLAUSES,
        "root_free_k7": ROOT_FREE_K7_CLAUSES,
        "root_containing_k6": ROOT_CONTAINING_K6_CLAUSES,
        "f7": F7_CLAUSES,
        "normalization_extras": len(EXTRA_CLAUSES),
        "master7": MASTER7_CLAUSES,
    }
    if result != expected:
        raise D7AuditError(f"degree-seven clause arithmetic changed: {result}")
    return result


def assignment_pair(assignment: dict[int, bool]) -> tuple[int, int]:
    return (
        sum(assignment[variable] for variable in range(12, 18)),
        sum(assignment[variable] for variable in range(18, 22)),
    )


def clause_satisfied(clause: Sequence[int], assignment: dict[int, bool]) -> bool:
    return any(assignment[abs(literal)] == (literal > 0) for literal in clause)


def satisfying_assignments(
    clauses: Sequence[Clause],
) -> tuple[dict[int, bool], ...]:
    result = []
    for values in itertools.product((False, True), repeat=10):
        assignment = dict(zip(range(12, 22), values))
        if all(clause_satisfied(clause, assignment) for clause in clauses):
            result.append(assignment)
    return tuple(result)


def is_prefix(values: Sequence[bool]) -> bool:
    return all(not right or left for left, right in zip(values, values[1:]))


def audit_extra_partition(
    clauses: Sequence[Clause] = EXTRA_CLAUSES,
    *,
    require_exact: bool = True,
) -> dict[str, object]:
    if tuple(global_edge(0, vertex) for vertex in range(1, 12)) != tuple(range(1, 12)):
        raise D7AuditError("root DIMACS variables changed")
    if tuple(global_edge(1, vertex) for vertex in range(2, 12)) != tuple(range(12, 22)):
        raise D7AuditError("second-centre DIMACS variables changed")
    for clause in clauses:
        if not clause or any(not 12 <= abs(literal) <= 21 for literal in clause):
            raise D7AuditError("normalization clause has an invalid literal")
        if len(set(clause)) != len(clause) or any(-literal in clause for literal in clause):
            raise D7AuditError("normalization clause is duplicate or tautological")
    models = satisfying_assignments(tuple(clauses))
    pairs = tuple(sorted(assignment_pair(model) for model in models))
    prefix = all(
        is_prefix(tuple(model[variable] for variable in range(12, 18)))
        and is_prefix(tuple(model[variable] for variable in range(18, 22)))
        for model in models
    )
    exact = len(models) == len(EXPECTED_PAIRS) and pairs == EXPECTED_PAIRS and prefix
    if require_exact and not exact:
        raise D7AuditError(
            f"normalization clauses do not encode the exact nine cases: {pairs}"
        )
    return {
        "models": len(models),
        "pairs": [list(pair) for pair in pairs],
        "all_models_are_two_sorted_prefixes": prefix,
        "exactly_nine_minimum_center_cases": exact,
    }


def _emit_compiled_catalogue(
    digest_f7: "hashlib._Hash",
    digest_master: "hashlib._Hash",
    variables: Sequence[int],
    compiled: Sequence[Sequence[tuple[int, bool]]],
    widths: Counter[int],
) -> tuple[int, int]:
    tokens = tuple((str(variable), f"-{variable}") for variable in variables)
    size = 0
    written = 0
    buffer: list[str] = []
    for specification in compiled:
        buffer.append(
            " ".join(
                tokens[position][1 if one else 0]
                for position, one in specification
            )
            + " 0\n"
        )
        widths[len(specification)] += 1
        written += 1
        if len(buffer) == 2_048:
            data = "".join(buffer).encode("ascii")
            digest_f7.update(data)
            digest_master.update(data)
            size += len(data)
            buffer.clear()
    if buffer:
        data = "".join(buffer).encode("ascii")
        digest_f7.update(data)
        digest_master.update(data)
        size += len(data)
    return written, size


def stream_fingerprints() -> dict[str, object]:
    counts = arithmetic_counts()
    blocks = block_catalogues()
    locals_ = local_catalogues()
    compiled_blocks = tuple(
        tuple(compiled_cube(cube, LOCAL_EDGES) for cube in catalogue)
        for catalogue in blocks
    )
    compiled_locals = tuple(
        tuple(compiled_cube(cube, 15) for cube in catalogue)
        for catalogue in locals_
    )

    digest_f7 = hashlib.sha256()
    digest_master = hashlib.sha256()
    header_f7 = f"p cnf {GLOBAL_VARIABLES} {F7_CLAUSES}\n".encode("ascii")
    header_master = f"p cnf {GLOBAL_VARIABLES} {MASTER7_CLAUSES}\n".encode("ascii")
    digest_f7.update(header_f7)
    digest_master.update(header_master)
    f7_bytes = len(header_f7)
    master_bytes = len(header_master)
    written = 0
    widths: Counter[int] = Counter()
    sections = Counter()

    for clause in base_clauses():
        data = clause_line(clause)
        digest_f7.update(data)
        digest_master.update(data)
        f7_bytes += len(data)
        master_bytes += len(data)
        widths[len(clause)] += 1
        written += 1
        sections["base"] += 1

    for vertices in itertools.combinations(range(1, 12), 7):
        neighbour_count = sum(vertex <= ROOT_DEGREE for vertex in vertices)
        amount, size = _emit_compiled_catalogue(
            digest_f7,
            digest_master,
            subset_variables(vertices),
            compiled_blocks[neighbour_count],
            widths,
        )
        written += amount
        sections["root_free_k7"] += amount
        f7_bytes += size
        master_bytes += size

    for vertices in itertools.combinations(range(1, 12), 6):
        neighbour_count = sum(vertex <= ROOT_DEGREE for vertex in vertices)
        amount, size = _emit_compiled_catalogue(
            digest_f7,
            digest_master,
            subset_variables(vertices),
            compiled_locals[neighbour_count],
            widths,
        )
        written += amount
        sections["root_containing_k6"] += amount
        f7_bytes += size
        master_bytes += size

    if written != F7_CLAUSES:
        raise D7AuditError(f"streamed F7 clause count changed: {written}")
    if dict(sections) != {
        "base": counts["base"],
        "root_free_k7": counts["root_free_k7"],
        "root_containing_k6": counts["root_containing_k6"],
    }:
        raise D7AuditError(f"streamed section counts changed: {dict(sections)}")
    f7_digest = digest_f7.hexdigest().upper()

    master_widths = widths.copy()
    for clause in EXTRA_CLAUSES:
        data = clause_line(clause)
        digest_master.update(data)
        master_bytes += len(data)
        master_widths[len(clause)] += 1
    master_digest = digest_master.hexdigest().upper()

    frozen = (
        EXPECTED_F7_BYTES,
        EXPECTED_F7_SHA256,
        EXPECTED_MASTER7_BYTES,
        EXPECTED_MASTER7_SHA256,
    )
    if any(item is not None for item in frozen):
        if None in frozen:
            raise D7AuditError("partial frozen fingerprint constants")
        if (f7_bytes, f7_digest, master_bytes, master_digest) != frozen:
            raise D7AuditError("degree-seven streamed fingerprint changed")

    return {
        "status": "PASS",
        "write_mode": "hash_only_no_cnf_written",
        "f7": {
            "variables": GLOBAL_VARIABLES,
            "clauses": written,
            "bytes": f7_bytes,
            "sha256": f7_digest,
            "widths": {
                str(width): amount for width, amount in sorted(widths.items())
            },
        },
        "master7_min_center": {
            "variables": GLOBAL_VARIABLES,
            "clauses": written + len(EXTRA_CLAUSES),
            "bytes": master_bytes,
            "sha256": master_digest,
            "widths": {
                str(width): amount
                for width, amount in sorted(master_widths.items())
            },
        },
    }


def full_audit() -> dict[str, object]:
    partition = audit_extra_partition()
    local_exactness = validate_local_cube_exactness()
    payloads = payload_audit()
    fingerprints = stream_fingerprints()
    return {
        "schema_version": 1,
        "status": "PASS_EXACT_D7_MIN_CENTER_SOURCE_AUDIT",
        "scope": (
            "Deterministic F7 and normalized-master clause stream, conditioned "
            "payloads, and finite ten-variable partition only; no SAT, LRAT, "
            "Lean theorem, global normalization theorem, or new Ramsey bound."
        ),
        "implementation": {
            "name": Path(__file__).name,
            "stdlib_only": True,
            "imports_project_generator": False,
            "writes_large_artifacts": False,
            "uses_solver": False,
            "uses_lrat": False,
        },
        "inputs": {
            "cover_tsv": COVER_TSV.name,
            "cover_tsv_sha256": file_sha256(COVER_TSV),
            "cover_records": list(read_cover_records()),
            "labelled_masks": len(forbidden_masks()),
            "labelled_mask_sha256": masks_digest(forbidden_masks()),
            "cube_closure": len(reduced_cubes()),
            "cube_closure_sha256": cubes_digest(reduced_cubes()),
        },
        "dimacs_convention": {
            "positive_literal": "edge present / raw graph6 adjacency bit 1",
            "variables": "row-major upper-triangle K12 edge variables, one-based",
            "root_edges": list(range(1, 12)),
            "root_assignment": {
                "positive_variables": list(range(1, ROOT_DEGREE + 1)),
                "negative_variables": list(range(ROOT_DEGREE + 1, 12)),
            },
            "center_to_root_neighbour_block": list(range(12, 18)),
            "center_to_root_nonneighbour_block": list(range(18, 22)),
            "root_variables_absent_from_f7_body": True,
            "blocker_polarity": "cube bit 1 becomes a negative literal; cube bit 0 becomes positive",
        },
        "normalization_boundary": {
            "external_mathematical_argument": (
                "In the seven-vertex root neighbourhood H, triangle-freeness "
                "and alpha(H)<=3 give Delta(H)<=3; odd order rules out all "
                "degrees 3, while R(3,3)=6 rules out an isolated vertex. "
                "A minimum-degree centre therefore has p in {1,2}. The global "
                "degree lower bound gives p+q>=2."
            ),
            "permutation_needed_before_using_f7": (
                "send a degree-seven root to vertex 0, a minimum-degree H "
                "vertex to 1, then sort the two remaining blocks"
            ),
            "formalized_here": False,
            "clauses": [list(clause) for clause in EXTRA_CLAUSES],
            "partition": partition,
        },
        "clause_arithmetic": arithmetic_counts(),
        "local_cube_exactness": local_exactness,
        "payloads": payloads,
        "fingerprints": fingerprints,
    }


def quick_audit() -> dict[str, object]:
    d8, d8_digest = read_d8_report()
    partition = audit_extra_partition()
    return {
        "status": "PASS",
        "clause_arithmetic": arithmetic_counts(),
        "partition": partition,
        "d8_report_sha256": d8_digest,
        "d8_cube_payloads": {
            "k7": d8["source_payloads"]["full_k7_conditioned_cubes"]["sha256"],
            "k6": d8["source_payloads"]["projected_k6_conditioned_cubes"]["sha256"],
        },
        "scope": "constant-time audit only; no catalogue or CNF stream reconstruction",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command",
        nargs="?",
        default="quick",
        choices=("quick", "payloads", "fingerprint", "audit", "emit-lean-payload"),
    )
    args = parser.parse_args()
    if args.command == "quick":
        result = quick_audit()
    elif args.command == "payloads":
        result = payload_audit()
    elif args.command == "fingerprint":
        result = stream_fingerprints()
    elif args.command == "emit-lean-payload":
        result = emit_lean_payload()
    else:
        result = full_audit()
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
