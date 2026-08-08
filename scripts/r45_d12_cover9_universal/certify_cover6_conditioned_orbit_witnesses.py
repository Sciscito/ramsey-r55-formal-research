#!/usr/bin/env python3
"""Certify compact S7 witnesses for the conditioned Master8 cube payloads.

The lazy Lean source stores 32,880 full K7 cubes and 1,200 projected K6
cubes.  This program links every positional entry to one of the six formal
cube representatives.  Each witness occupies exactly fifteen packed bits:

    representative_index + 6 * lexicographic_S7_permutation_rank.

The consecutive 15-bit words are exposed through a URL-safe 64-symbol sextet
stream, so two witnesses occupy five ASCII characters.  For a K7 row,
applying the decoded permutation to the decoded representative
must reproduce the source cube.  For a projected K6 row, it reconstructs a
deterministically selected compatible full K7 lift, whose projection must
reproduce the source cube.  Thus no separate 42-bit full-lift table is needed.

This is a deterministic finite-data certificate.  It imports the existing
exact replay and cube/motif bridge, invokes no solver, and writes only when the
explicit ``write-tracked`` command is requested.
"""

from __future__ import annotations

import argparse
import functools
import hashlib
import itertools
import json
import math
import re
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable, Sequence

from . import analyze_master8_core_taxonomy as taxonomy
from . import certify_cover6_cube_motif_bridge as bridge
from . import exact_replay_cover6_d8 as replay


HERE = Path(__file__).resolve().parent
REPORT_NAME = "COVER6_CONDITIONED_ORBIT_WITNESSES_V1.json"
INDEXED_SOURCE = (
    HERE.parent.parent
    / "vendor"
    / "lrat-catcher"
    / "LRATCatcher"
    / "Tests"
    / "R44Cover6Master8IndexedSource.lean"
)

ALPHABET = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz-_"
ALPHABET_INDEX = {character: index for index, character in enumerate(ALPHABET)}
WITNESS_BITS = 15
CUBE_DIGITS = 7
REPORT_CHUNK_SIZE = 4060
PERMUTATION_COUNT = math.factorial(replay.LOCAL_ORDER)
WITNESS_LIMIT = len(replay.CUBE_REPRESENTATIVES) * PERMUTATION_COUNT

BLOCK_NEIGHBOUR_COUNTS = (4, 5, 6, 7)
LOCAL_NEIGHBOUR_COUNTS = (3, 4, 5)
BLOCK_COUNTS = (15_480, 10_200, 4_680, 2_520)
LOCAL_COUNTS = (540, 360, 300)
BLOCK_ENTRIES = sum(BLOCK_COUNTS)
LOCAL_ENTRIES = sum(LOCAL_COUNTS)

BLOCK_CUBE_PAYLOAD_SHA256 = (
    "98B76E3BA2E3A8AF897C44572040F07690D1D5A9050B78B8AF28703FC77D01D1"
)
LOCAL_CUBE_PAYLOAD_SHA256 = (
    "E2DCE6964D99B6F94D0F12A35E12BC5B53677F60215CA44F23CDE0F290FC5BBB"
)

Cube = replay.Cube
Witness = tuple[int, int]


class ConditionedWitnessError(ValueError):
    """Raised at the first malformed or semantically false witness."""


def sha256_ascii(payload: str) -> str:
    return hashlib.sha256(payload.encode("ascii")).hexdigest().upper()


def digest_lines(lines: Iterable[str]) -> str:
    return sha256_ascii("".join(lines))


def encode_base64_le(value: int, digits: int) -> str:
    if value < 0 or value >= 1 << (6 * digits):
        raise ConditionedWitnessError(
            f"value {value} does not fit in {digits} base64 digits"
        )
    return "".join(ALPHABET[(value >> (6 * digit)) & 63] for digit in range(digits))


def decode_base64_le(payload: str) -> int:
    value = 0
    for digit, character in enumerate(payload):
        try:
            component = ALPHABET_INDEX[character]
        except KeyError as error:
            raise ConditionedWitnessError(
                f"character {character!r} is outside the frozen alphabet"
            ) from error
        value += component << (6 * digit)
    return value


def encode_cube(cube: Cube) -> str:
    ones, fixed = cube
    if ones & ~fixed or fixed & ~replay.LOCAL_FULL:
        raise ConditionedWitnessError(f"malformed full K7 cube: {cube!r}")
    return encode_base64_le(ones + (fixed << replay.LOCAL_EDGES), CUBE_DIGITS)


def decode_cube(payload: str) -> Cube:
    if len(payload) != CUBE_DIGITS:
        raise ConditionedWitnessError("a packed cube must contain seven digits")
    packed = decode_base64_le(payload)
    cube = packed & replay.LOCAL_FULL, packed >> replay.LOCAL_EDGES
    if cube[0] & ~cube[1] or cube[1] & ~replay.LOCAL_FULL:
        raise ConditionedWitnessError("packed cube violates ones subset fixed")
    return cube


def permutation_rank(permutation: Sequence[int]) -> int:
    if len(permutation) != replay.LOCAL_ORDER:
        raise ConditionedWitnessError("an S7 permutation must have seven entries")
    remaining = list(range(replay.LOCAL_ORDER))
    rank = 0
    for position, value in enumerate(permutation):
        try:
            digit = remaining.index(value)
        except ValueError as error:
            raise ConditionedWitnessError("not a permutation of range(7)") from error
        rank += digit * math.factorial(replay.LOCAL_ORDER - position - 1)
        remaining.pop(digit)
    return rank


def permutation_unrank(rank: int) -> tuple[int, ...]:
    if not 0 <= rank < PERMUTATION_COUNT:
        raise ConditionedWitnessError(f"S7 rank out of range: {rank}")
    remaining = list(range(replay.LOCAL_ORDER))
    result = []
    residual = rank
    for position in range(replay.LOCAL_ORDER):
        factor = math.factorial(replay.LOCAL_ORDER - position - 1)
        digit, residual = divmod(residual, factor)
        result.append(remaining.pop(digit))
    return tuple(result)


def witness_code(representative_index: int, permutation_index: int) -> int:
    if not 0 <= representative_index < len(replay.CUBE_REPRESENTATIVES):
        raise ConditionedWitnessError(
            f"representative index out of range: {representative_index}"
        )
    if not 0 <= permutation_index < PERMUTATION_COUNT:
        raise ConditionedWitnessError(
            f"permutation rank out of range: {permutation_index}"
        )
    return representative_index + len(replay.CUBE_REPRESENTATIVES) * permutation_index


def decode_witness_code(packed: int) -> Witness:
    if not 0 <= packed < WITNESS_LIMIT:
        raise ConditionedWitnessError(f"unused witness code: {packed}")
    return (
        packed % len(replay.CUBE_REPRESENTATIVES),
        packed // len(replay.CUBE_REPRESENTATIVES),
    )


def packed_sextet_length(entries: int) -> int:
    if entries < 0:
        raise ConditionedWitnessError("negative witness count")
    return (entries * WITNESS_BITS + 5) // 6


def pack_witnesses(witnesses: Sequence[Witness]) -> str:
    """Pack consecutive 15-bit words into a little-endian sextet stream."""
    accumulator = 0
    available = 0
    output = []
    for representative_index, permutation_index in witnesses:
        accumulator |= witness_code(representative_index, permutation_index) << available
        available += WITNESS_BITS
        while available >= 6:
            output.append(ALPHABET[accumulator & 63])
            accumulator >>= 6
            available -= 6
    if available:
        output.append(ALPHABET[accumulator & 63])
    payload = "".join(output)
    if len(payload) != packed_sextet_length(len(witnesses)):
        raise ConditionedWitnessError("packed witness length arithmetic failed")
    return payload


def witness_at(payload: str, item: int, entries: int) -> Witness:
    if len(payload) != packed_sextet_length(entries):
        raise ConditionedWitnessError("packed witness stream length mismatch")
    if not 0 <= item < entries:
        raise ConditionedWitnessError(f"witness item out of range: {item}")
    bit_start = item * WITNESS_BITS
    digit_start, shift = divmod(bit_start, 6)
    # Since 15 mod 6 = 3, each word starts at bit offset zero or three and
    # always fits in exactly three adjacent sextets.
    window = decode_base64_le(payload[digit_start : digit_start + 3])
    return decode_witness_code((window >> shift) & ((1 << WITNESS_BITS) - 1))


def unpack_witnesses(payload: str, entries: int) -> tuple[Witness, ...]:
    result = tuple(witness_at(payload, item, entries) for item in range(entries))
    # Repacking catches nonzero padding bits for odd-sized synthetic streams.
    if pack_witnesses(result) != payload:
        raise ConditionedWitnessError("noncanonical witness padding bits")
    return result


@functools.cache
def permutations() -> tuple[tuple[int, ...], ...]:
    result = tuple(itertools.permutations(range(replay.LOCAL_ORDER)))
    if len(result) != PERMUTATION_COUNT:
        raise ConditionedWitnessError("S7 enumeration length changed")
    if any(permutation_rank(item) != rank for rank, item in enumerate(result)):
        raise ConditionedWitnessError("Lehmer rank differs from itertools order")
    return result


def transform_cube(cube: Cube, permutation_index: int) -> Cube:
    if not 0 <= permutation_index < PERMUTATION_COUNT:
        raise ConditionedWitnessError(
            f"permutation rank out of range: {permutation_index}"
        )
    try:
        mapping = replay.permutation_maps()[permutation_index]
    except IndexError as error:
        raise ConditionedWitnessError(
            f"permutation rank out of range: {permutation_index}"
        ) from error
    return replay.transform(cube[0], mapping), replay.transform(cube[1], mapping)


def cube_from_witness(witness: Witness) -> Cube:
    representative_index, permutation_index = witness
    witness_code(representative_index, permutation_index)
    representative = replay.CUBE_REPRESENTATIVES[representative_index]
    return transform_cube(representative, permutation_index)


def verify_cube_witness(cube: Cube, witness: Witness) -> Witness:
    reconstructed = cube_from_witness(witness)
    if reconstructed != cube:
        raise ConditionedWitnessError(
            f"witness reconstructs {reconstructed!r}, expected {cube!r}"
        )
    return witness


def verify_projected_lift_witness(
    projected: Cube, neighbour_count: int, witness: Witness
) -> tuple[Witness, Cube]:
    full = cube_from_witness(witness)
    if not bridge.compatible_with_root(full, neighbour_count):
        raise ConditionedWitnessError("decoded full lift contradicts fixed root edges")
    observed = replay.project_nonroot(full[0]), replay.project_nonroot(full[1])
    if observed != projected:
        raise ConditionedWitnessError(
            f"decoded full lift projects to {observed!r}, expected {projected!r}"
        )
    return witness, full


@functools.cache
def orbit_witness_index() -> dict[Cube, Witness]:
    """Return the least lexicographic S7 witness for every full orbit cube."""
    result: dict[Cube, Witness] = {}
    owner: dict[Cube, int] = {}
    for representative_index, representative in enumerate(replay.CUBE_REPRESENTATIVES):
        for permutation_index, mapping in enumerate(replay.permutation_maps()):
            cube = (
                replay.transform(representative[0], mapping),
                replay.transform(representative[1], mapping),
            )
            previous_owner = owner.get(cube)
            if previous_owner is not None and previous_owner != representative_index:
                raise ConditionedWitnessError("the six representative orbits overlap")
            owner[cube] = representative_index
            result.setdefault(cube, (representative_index, permutation_index))
    expected = set(replay.reduced_cubes())
    if set(result) != expected:
        raise ConditionedWitnessError("witness index differs from reduced cube closure")
    if Counter(owner.values()) != Counter(dict(enumerate(replay.CUBE_ORBIT_SIZES))):
        raise ConditionedWitnessError("representative orbit sizes changed")
    return result


def block_catalogue_sections() -> tuple[tuple[int, tuple[Cube, ...]], ...]:
    catalogues = replay.block_conditioned_cubes()
    result = tuple((count, catalogues[count]) for count in BLOCK_NEIGHBOUR_COUNTS)
    if tuple(len(cubes) for _count, cubes in result) != BLOCK_COUNTS:
        raise ConditionedWitnessError("reachable K7 catalogue counts changed")
    return result


def local_catalogue_sections() -> tuple[tuple[int, tuple[Cube, ...]], ...]:
    catalogues = replay.local_conditioned_cubes()
    result = tuple((count, catalogues[count]) for count in LOCAL_NEIGHBOUR_COUNTS)
    if tuple(len(cubes) for _count, cubes in result) != LOCAL_COUNTS:
        raise ConditionedWitnessError("reachable projected K6 catalogue counts changed")
    return result


def flatten_sections(
    sections: Sequence[tuple[int, Sequence[Cube]]],
) -> tuple[tuple[int, int, Cube], ...]:
    return tuple(
        (neighbour_count, local_index, cube)
        for neighbour_count, cubes in sections
        for local_index, cube in enumerate(cubes)
    )


def encode_cube_sections(sections: Sequence[tuple[int, Sequence[Cube]]]) -> str:
    return "".join(encode_cube(cube) for _count, cubes in sections for cube in cubes)


def extract_lean_string_array(source: str, definition: str) -> tuple[str, ...]:
    pattern = re.compile(
        rf"def\s+{re.escape(definition)}\s*:\s*Array\s+String\s*:=\s*#\[(.*?)\n\]",
        re.DOTALL,
    )
    match = pattern.search(source)
    if match is None:
        raise ConditionedWitnessError(f"Lean array {definition} not found")
    chunks = tuple(re.findall(r'"([0-9A-Za-z_-]*)"', match.group(1)))
    if not chunks:
        raise ConditionedWitnessError(f"Lean array {definition} has no chunks")
    residue = re.sub(r'"[0-9A-Za-z_-]*"|[\s,]', "", match.group(1))
    if residue:
        raise ConditionedWitnessError(
            f"unexpected syntax in Lean array {definition}: {residue[:40]!r}"
        )
    return chunks


def require_exact_cube_payload(
    payload: str, entries: int, expected_sha256: str, label: str
) -> None:
    if len(payload) != entries * CUBE_DIGITS:
        raise ConditionedWitnessError(f"{label} cube payload length changed")
    if sha256_ascii(payload) != expected_sha256:
        raise ConditionedWitnessError(f"{label} cube payload SHA-256 changed")


def indexed_source_payloads(path: Path = INDEXED_SOURCE) -> tuple[str, str]:
    source = path.read_text(encoding="utf-8")
    block = "".join(extract_lean_string_array(source, "blockCubeDataChunks"))
    local = "".join(extract_lean_string_array(source, "localCubeDataChunks"))
    require_exact_cube_payload(
        block, BLOCK_ENTRIES, BLOCK_CUBE_PAYLOAD_SHA256, "Lean K7"
    )
    require_exact_cube_payload(
        local, LOCAL_ENTRIES, LOCAL_CUBE_PAYLOAD_SHA256, "Lean K6"
    )
    return block, local


def extract_lean_nat_array(source: str, definition: str) -> tuple[int, ...]:
    pattern = re.compile(
        rf"def\s+{re.escape(definition)}\s*:\s*Array\s+Nat\s*:=\s*#\[(.*?)\n\]",
        re.DOTALL,
    )
    match = pattern.search(source)
    if match is None:
        raise ConditionedWitnessError(f"Lean Nat array {definition} not found")
    residue = re.sub(r"[0-9\s,]", "", match.group(1))
    if residue:
        raise ConditionedWitnessError(
            f"unexpected syntax in Lean Nat array {definition}: {residue[:40]!r}"
        )
    return tuple(map(int, re.findall(r"\d+", match.group(1))))


def indexed_source_core_master_indices(
    path: Path = INDEXED_SOURCE,
) -> tuple[int, ...]:
    source = path.read_text(encoding="utf-8")
    indices = extract_lean_nat_array(source, "coreMasterZeroBasedIndices")
    if len(indices) != taxonomy.CORE_CLAUSES:
        raise ConditionedWitnessError("Lean core index count changed")
    if any(left >= right for left, right in zip(indices, indices[1:])):
        raise ConditionedWitnessError("Lean core indices are not strictly increasing")
    return indices


def normalized_index_of_master(master_zero_based: int) -> int:
    if master_zero_based < replay.SOURCE_CLAUSES:
        return master_zero_based
    mapping = {
        master_id - 1: replay.SOURCE_CLAUSES + position
        for position, master_id in enumerate(taxonomy.CORE8_EXTRA_MASTER_IDS)
    }
    try:
        return mapping[master_zero_based]
    except KeyError as error:
        raise ConditionedWitnessError(
            f"core Master8 extra has no normalized index: {master_zero_based}"
        ) from error


def catalogue_offsets(
    neighbour_counts: Sequence[int], counts: Sequence[int]
) -> dict[int, int]:
    result: dict[int, int] = {}
    offset = 0
    for neighbour_count, count in zip(neighbour_counts, counts):
        result[neighbour_count] = offset
        offset += count
    return result


def core_specific_view(
    block_sections: Sequence[tuple[int, Sequence[Cube]]],
    local_sections: Sequence[tuple[int, Sequence[Cube]]],
    block_witnesses: Sequence[Witness],
    lift_rows: Sequence[tuple[int, int, Cube, Cube, int, Witness]],
    indexed_source: Path = INDEXED_SOURCE,
) -> dict[str, object]:
    """Hash the ordered blocker view induced by coreNormalizedFinIndices."""
    rows = taxonomy.core_rows()
    lean_master_indices = indexed_source_core_master_indices(indexed_source)
    expected_master_indices = tuple(row.master_id - 1 for row in rows)
    if lean_master_indices != expected_master_indices:
        raise ConditionedWitnessError(
            "taxonomy core order differs from Lean coreMasterZeroBasedIndices"
        )
    normalized_indices = tuple(normalized_index_of_master(index) for index in lean_master_indices)
    if any(not 0 <= index < taxonomy.CORE8_CLAUSES for index in normalized_indices):
        raise ConditionedWitnessError("normalized core index is out of range")

    block_by_count = dict(block_sections)
    local_by_count = dict(local_sections)
    block_offsets = catalogue_offsets(BLOCK_NEIGHBOUR_COUNTS, BLOCK_COUNTS)
    local_offsets = catalogue_offsets(LOCAL_NEIGHBOUR_COUNTS, LOCAL_COUNTS)
    block_subsets = {
        vertices: index
        for index, vertices in enumerate(itertools.combinations(range(1, 12), 7))
    }
    local_subsets = {
        vertices: index
        for index, vertices in enumerate(itertools.combinations(range(1, 12), 6))
    }
    lift_by_payload = {
        local_offsets[count] + local_index: row
        for row in lift_rows
        for count, local_index in [(row[0], row[1])]
    }

    block_lines: list[str] = []
    local_lines: list[str] = []
    blocker_core_ids = []
    for row, normalized_index in zip(rows, normalized_indices):
        location = row.location
        if location.family not in ("root_free_blocker", "root_containing_blocker"):
            continue
        if location.condition is None or location.template_position is None:
            raise ConditionedWitnessError("conditioned core row lacks coordinates")
        condition = location.condition
        catalogue_index = location.template_position - 1
        vertices_text = ",".join(map(str, location.vertices))
        blocker_core_ids.append(row.core_id)
        if location.family == "root_free_blocker":
            cubes = block_by_count[condition]
            cube = cubes[catalogue_index]
            payload_index = block_offsets[condition] + catalogue_index
            witness = block_witnesses[payload_index]
            verify_cube_witness(cube, witness)
            subset_index = block_subsets[location.vertices]
            clause = replay.instantiate(cube, replay.subset_variables(location.vertices))
            if clause != row.clause:
                raise ConditionedWitnessError(
                    f"K7 core clause reconstruction failed at core row {row.core_id}"
                )
            block_lines.append(
                f"{row.core_id}\t{normalized_index}\t{subset_index}\t{vertices_text}\t"
                f"{condition}\t{catalogue_index}\t{payload_index}\t"
                f"{cube[0]:06X}\t{cube[1]:06X}\t{witness[0]}\t{witness[1]}\n"
            )
        else:
            cubes = local_by_count[condition]
            projected = cubes[catalogue_index]
            payload_index = local_offsets[condition] + catalogue_index
            lift_row = lift_by_payload[payload_index]
            if lift_row[:3] != (condition, catalogue_index, projected):
                raise ConditionedWitnessError("K6 canonical lift payload order changed")
            full, multiplicity, witness = lift_row[3], lift_row[4], lift_row[5]
            verify_projected_lift_witness(projected, condition, witness)
            subset_index = local_subsets[location.vertices]
            clause = replay.instantiate(projected, replay.subset_variables(location.vertices))
            if clause != row.clause:
                raise ConditionedWitnessError(
                    f"K6 core clause reconstruction failed at core row {row.core_id}"
                )
            local_lines.append(
                f"{row.core_id}\t{normalized_index}\t{subset_index}\t{vertices_text}\t"
                f"{condition}\t{catalogue_index}\t{payload_index}\t"
                f"{projected[0]:06X}\t{projected[1]:06X}\t"
                f"{full[0]:06X}\t{full[1]:06X}\t{multiplicity}\t"
                f"{witness[0]}\t{witness[1]}\n"
            )

    if (len(block_lines), len(local_lines)) != (3_514, 2_409):
        raise ConditionedWitnessError("conditioned dependency-core counts changed")
    combined = tuple(
        line for _core_id, line in sorted(
            (
                (int(line.split("\t", 1)[0]), line)
                for line in (*block_lines, *local_lines)
            ),
            key=lambda item: item[0],
        )
    )
    if [int(line.split("\t", 1)[0]) for line in combined] != blocker_core_ids:
        raise ConditionedWitnessError("core blocker merge order changed")
    return {
        "ordering": (
            "core_clause_id order, exactly coreNormalizedFinIndices order; blocker "
            "indices are unchanged by Master8-to-core8 normalization"
        ),
        "all_6152_master_indices_equal_actual_lean_array": True,
        "normalized_zero_based_indices_sha256": digest_lines(
            f"{index}\n" for index in normalized_indices
        ),
        "retained_full_k7_blockers": len(block_lines),
        "retained_projected_k6_blockers": len(local_lines),
        "retained_conditioned_blockers": len(combined),
        "all_instantiated_clauses_equal_core_rows": True,
        "full_k7_ordered_view_sha256": sha256_ascii("".join(block_lines)),
        "projected_k6_ordered_view_sha256": sha256_ascii("".join(local_lines)),
        "combined_core_ordered_view_sha256": sha256_ascii("".join(combined)),
        "view_fields": {
            "full_k7": [
                "core_id", "normalized_zero_based_index", "subset_index",
                "embedding_vertices", "condition", "catalogue_index", "payload_index",
                "ones", "fixed", "representative", "permutation_rank",
            ],
            "projected_k6": [
                "core_id", "normalized_zero_based_index", "subset_index",
                "embedding_vertices", "condition", "catalogue_index", "payload_index",
                "projected_ones", "projected_fixed", "full_ones", "full_fixed",
                "lift_multiplicity", "representative", "permutation_rank",
            ],
        },
        "additional_payload_required": False,
        "reconstruction": (
            "derive subset/embedding and catalogue position from each normalized core "
            "index, then index the existing conditioned cube and witness streams"
        ),
    }


def canonical_lift_rows(
    sections: Sequence[tuple[int, Sequence[Cube]]],
) -> tuple[tuple[int, int, Cube, Cube, int, Witness], ...]:
    """Choose min (fixed, ones) full lifts, matching the existing bridge."""
    _orbits, owner = bridge.cube_data()
    result = []
    for neighbour_count, cubes in sections:
        lifts = bridge.root_containing_lifts(owner, neighbour_count)
        for local_index, projected in enumerate(cubes):
            candidates = lifts[projected]
            if candidates != tuple(sorted(candidates, key=lambda cube: (cube[1], cube[0]))):
                raise ConditionedWitnessError("full lifts are not canonically ordered")
            owners = {owner[candidate] for candidate in candidates}
            if len(owners) != 1:
                raise ConditionedWitnessError("projected cube has ambiguous orbit provenance")
            full = candidates[0]
            witness = orbit_witness_index()[full]
            result.append(
                (neighbour_count, local_index, projected, full, len(candidates), witness)
            )
    if len(result) != LOCAL_ENTRIES:
        raise ConditionedWitnessError("canonical K6 lift row count changed")
    return tuple(result)


def chunks(payload: str) -> list[str]:
    return [
        payload[offset : offset + REPORT_CHUNK_SIZE]
        for offset in range(0, len(payload), REPORT_CHUNK_SIZE)
    ]


def witness_statistics(witnesses: Sequence[Witness]) -> dict[str, object]:
    representatives = Counter(representative for representative, _rank in witnesses)
    ranks = [rank for _representative, rank in witnesses]
    return {
        "representative_counts": {
            str(index): representatives[index]
            for index in range(len(replay.CUBE_REPRESENTATIVES))
        },
        "minimum_permutation_rank": min(ranks),
        "maximum_permutation_rank": max(ranks),
        "distinct_witness_codes": len(set(witnesses)),
    }


def build_report(indexed_source: Path = INDEXED_SOURCE) -> dict[str, object]:
    if ALPHABET != "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz-_":
        raise ConditionedWitnessError("base64url alphabet changed")
    if WITNESS_LIMIT > 1 << WITNESS_BITS:
        raise ConditionedWitnessError("fifteen witness bits are no longer sufficient")
    permutations()

    block_sections = block_catalogue_sections()
    local_sections = local_catalogue_sections()
    block_rows = flatten_sections(block_sections)
    local_rows = flatten_sections(local_sections)

    generated_block_cubes = encode_cube_sections(block_sections)
    generated_local_cubes = encode_cube_sections(local_sections)
    lean_block_cubes, lean_local_cubes = indexed_source_payloads(indexed_source)
    if generated_block_cubes != lean_block_cubes:
        raise ConditionedWitnessError(
            "generated K7 catalogue differs element-by-element from Lean payload"
        )
    if generated_local_cubes != lean_local_cubes:
        raise ConditionedWitnessError(
            "generated K6 catalogue differs element-by-element from Lean payload"
        )

    witness_index = orbit_witness_index()
    block_witnesses = tuple(witness_index[cube] for _count, _index, cube in block_rows)
    block_payload = pack_witnesses(block_witnesses)
    decoded_block_witnesses = unpack_witnesses(block_payload, BLOCK_ENTRIES)
    if decoded_block_witnesses != block_witnesses:
        raise ConditionedWitnessError("K7 witness stream round trip changed rows")
    for (_count, _index, cube), witness in zip(block_rows, block_witnesses):
        verify_cube_witness(cube, witness)

    lift_rows = canonical_lift_rows(local_sections)
    local_witnesses = tuple(row[-1] for row in lift_rows)
    local_payload = pack_witnesses(local_witnesses)
    decoded_local_witnesses = unpack_witnesses(local_payload, LOCAL_ENTRIES)
    if decoded_local_witnesses != local_witnesses:
        raise ConditionedWitnessError("K6 witness stream round trip changed rows")
    for row, witness in zip(lift_rows, local_witnesses):
        neighbour_count, _index, projected, expected_full, _multiplicity, witness = row
        observed_witness, observed_full = verify_projected_lift_witness(
            projected, neighbour_count, witness
        )
        if observed_witness != witness or observed_full != expected_full:
            raise ConditionedWitnessError("encoded K6 lift witness is not canonical")

    block_section_stats = []
    offset = 0
    for neighbour_count, cubes in block_sections:
        amount = len(cubes)
        section_witnesses = block_witnesses[offset : offset + amount]
        section_payload = pack_witnesses(section_witnesses)
        block_section_stats.append({
            "root_neighbours_in_seven_set": neighbour_count,
            "entries": amount,
            "cube_sha256": replay.cubes_digest(cubes),
            "witness_sha256": sha256_ascii(section_payload),
            **witness_statistics(section_witnesses),
        })
        offset += amount

    local_section_stats = []
    offset = 0
    for neighbour_count, cubes in local_sections:
        section_rows = [row for row in lift_rows if row[0] == neighbour_count]
        amount = len(section_rows)
        section_witnesses = local_witnesses[offset : offset + amount]
        section_payload = pack_witnesses(section_witnesses)
        multiplicities = Counter(row[4] for row in section_rows)
        local_section_stats.append({
            "root_neighbours_among_six_vertices": neighbour_count,
            "entries": amount,
            "projected_cube_sha256": replay.cubes_digest(cubes),
            "witness_sha256": sha256_ascii(section_payload),
            "full_lift_multiplicity_counts": {
                str(value): count for value, count in sorted(multiplicities.items())
            },
            "unique_full_lifts_within_reduced_cube_family": multiplicities.get(1, 0),
            **witness_statistics(section_witnesses),
        })
        offset += amount

    multiplicities = Counter(row[4] for row in lift_rows)
    block_row_digest = digest_lines(
        f"{count}\t{index}\t{cube[0]:06X}\t{cube[1]:06X}\t"
        f"{witness[0]}\t{witness[1]}\n"
        for (count, index, cube), witness in zip(block_rows, block_witnesses)
    )
    local_row_digest = digest_lines(
        f"{count}\t{index}\t{projected[0]:06X}\t{projected[1]:06X}\t"
        f"{full[0]:06X}\t{full[1]:06X}\t{multiplicity}\t"
        f"{witness[0]}\t{witness[1]}\n"
        for count, index, projected, full, multiplicity, witness in lift_rows
    )
    core_view = core_specific_view(
        block_sections,
        local_sections,
        block_witnesses,
        lift_rows,
        indexed_source,
    )

    return {
        "schema_version": 1,
        "status": "PASS_EXACT_CONDITIONED_ORBIT_WITNESSES",
        "scope": (
            "Exact finite positional witnesses for the conditioned cube payloads; "
            "no SAT, LRAT, graph-to-CNF satisfaction theorem, or cover6-d8 theorem."
        ),
        "implementation": {
            "name": Path(__file__).name,
            "imports": [
                "exact_replay_cover6_d8.py",
                "certify_cover6_cube_motif_bridge.py",
                "analyze_master8_core_taxonomy.py",
            ],
            "common_mode_boundary": (
                "Catalogue generation, projection, and S7 action reuse the existing "
                "Python replay/bridge; this is not an independent derivation of them."
            ),
            "indexed_source_module": (
                "vendor/lrat-catcher/LRATCatcher/Tests/"
                "R44Cover6Master8IndexedSource.lean"
            ),
        },
        "source_payloads": {
            "full_k7_conditioned_cubes": {
                "lean_definition": "blockCubeDataChunks",
                "neighbour_counts": list(BLOCK_NEIGHBOUR_COUNTS),
                "section_entries": list(BLOCK_COUNTS),
                "entries": BLOCK_ENTRIES,
                "digits_per_cube": CUBE_DIGITS,
                "ascii_characters": len(generated_block_cubes),
                "sha256": sha256_ascii(generated_block_cubes),
                "generated_equals_lean_payload": True,
            },
            "projected_k6_conditioned_cubes": {
                "lean_definition": "localCubeDataChunks",
                "neighbour_counts": list(LOCAL_NEIGHBOUR_COUNTS),
                "section_entries": list(LOCAL_COUNTS),
                "entries": LOCAL_ENTRIES,
                "digits_per_cube": CUBE_DIGITS,
                "ascii_characters": len(generated_local_cubes),
                "sha256": sha256_ascii(generated_local_cubes),
                "generated_equals_lean_payload": True,
            },
        },
        "encoding": {
            "alphabet": ALPHABET,
            "bitstream_endianness": (
                "little-endian 15-bit words concatenated least-significant bit first, "
                "then emitted as little-endian 6-bit URL-safe alphabet digits"
            ),
            "permutation_enumeration": (
                "Python itertools.permutations(range(7)) lexicographic order"
            ),
            "permutation_rank": "zero-based Lehmer rank",
            "action": (
                "target edge (u,v) receives source bit at (perm[u],perm[v]); "
                "identical to permuteLocalMask in R44Cover6S7Transport"
            ),
            "packed_witness": "representative_index + 6 * permutation_rank",
            "bits_per_witness": WITNESS_BITS,
            "logical_bytes_per_witness": WITNESS_BITS / 8,
            "ascii_characters_per_two_witnesses": 5,
            "available_codes": 1 << WITNESS_BITS,
            "valid_code_range": [0, WITNESS_LIMIT - 1],
            "representative_range": [0, 5],
            "permutation_rank_range": [0, PERMUTATION_COUNT - 1],
            "selection_rule": (
                "least lexicographic permutation rank producing the full cube"
            ),
        },
        "full_k7_orbit_witnesses": {
            "entries": BLOCK_ENTRIES,
            "ascii_characters": len(block_payload),
            "sha256": sha256_ascii(block_payload),
            "semantic_rows_sha256": block_row_digest,
            "all_reconstruct_exact_source_cube": True,
            "sections": block_section_stats,
            **witness_statistics(block_witnesses),
        },
        "projected_k6_canonical_lift_orbit_witnesses": {
            "entries": LOCAL_ENTRIES,
            "ascii_characters": len(local_payload),
            "sha256": sha256_ascii(local_payload),
            "semantic_rows_sha256": local_row_digest,
            "canonical_full_lift_order": "minimum (full_fixed_mask, full_ones_mask)",
            "canonical_selection_is_deterministic": True,
            "all_lifts_compatible_with_fixed_root_edges": True,
            "all_lifts_project_to_exact_source_cube": True,
            "all_projected_cubes_have_unique_representative_provenance": True,
            "all_full_lifts_unique_within_reduced_cube_family": (
                multiplicities.get(1, 0) == LOCAL_ENTRIES
            ),
            "unique_full_lifts_within_reduced_cube_family": multiplicities.get(1, 0),
            "full_lift_multiplicity_counts": {
                str(value): count for value, count in sorted(multiplicities.items())
            },
            "stored_full_cube_digits_per_row": 0,
            "full_lift_reconstruction": (
                "apply the decoded S7 permutation to the decoded representative"
            ),
            "sections": local_section_stats,
            **witness_statistics(local_witnesses),
        },
        "compression": {
            "total_entries": BLOCK_ENTRIES + LOCAL_ENTRIES,
            "witness_ascii_characters": len(block_payload) + len(local_payload),
            "packed_logical_bytes": (
                (BLOCK_ENTRIES + LOCAL_ENTRIES) * WITNESS_BITS // 8
            ),
            "logical_bytes_per_witness": WITNESS_BITS / 8,
            "ascii_characters_per_witness": (
                (len(block_payload) + len(local_payload))
                / (BLOCK_ENTRIES + LOCAL_ENTRIES)
            ),
            "fixed_width_bits_per_witness": WITNESS_BITS,
            "information_bits_needed_for_30240_codes": math.ceil(
                math.log2(WITNESS_LIMIT)
            ),
            "avoided_k6_full_lift_ascii_characters": LOCAL_ENTRIES * CUBE_DIGITS,
            "payload_container": (
                f"JSON strings split into at most {REPORT_CHUNK_SIZE}-character chunks"
            ),
        },
        "certificate_payloads": {
            "full_k7_witness_chunks": chunks(block_payload),
            "projected_k6_lift_witness_chunks": chunks(local_payload),
        },
        "normalized_core_specific_ordered_view": core_view,
        "lean_integration_boundary": {
            "sufficient_checks": [
                "at item i, read the 15 bits starting at bit offset 15*i and reject codes >= 30240",
                "unrank the S7 permutation in lexicographic order",
                "for K7, prove decoded source cube = permuteCube permutation representative",
                "for K6, reconstruct the full cube, check root compatibility, and prove its projection equals the decoded source cube",
                "feed the resulting CubeInOrbitOf witness to orbitCube_forces_motif",
            ],
            "python_checks_actual_lean_cube_payload_bytes": True,
            "not_yet_a_lean_theorem": True,
            "honest_boundary": (
                "The JSON witnesses and Python verification do not by themselves enter "
                "Lean's trusted proof. A Lean decoder plus finite equality checks remain "
                "necessary before using these witnesses in the graph-level satisfaction proof."
            ),
        },
    }


def tracked_report() -> dict[str, object]:
    return json.loads((HERE / REPORT_NAME).read_text(encoding="utf-8"))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command",
        choices=("summary", "report", "verify-tracked", "write-tracked"),
        nargs="?",
        default="summary",
    )
    args = parser.parse_args()
    report = build_report()
    if args.command == "verify-tracked":
        if report != tracked_report():
            raise ConditionedWitnessError("generated report differs from tracked report")
        output: object = {"status": "PASS", "report": REPORT_NAME}
    elif args.command == "write-tracked":
        target = HERE / REPORT_NAME
        target.write_text(
            json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        output = {"status": "WROTE", "report": REPORT_NAME}
    elif args.command == "summary":
        output = {
            "status": report["status"],
            "k7": report["full_k7_orbit_witnesses"],
            "k6": report["projected_k6_canonical_lift_orbit_witnesses"],
            "compression": report["compression"],
        }
        # Keep the default command readable: payload chunks are available via
        # ``report`` or the tracked JSON, not repeated in the terminal.
        for section in (output["k7"], output["k6"]):
            if isinstance(section, dict):
                section.pop("sections", None)
    else:
        output = report
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
