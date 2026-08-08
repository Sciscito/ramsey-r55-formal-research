#!/usr/bin/env python3
"""Classify the 6,152 Master8 dependency-core clauses declaratively.

The LRAT reducer records the original one-based Master8 clause identifier for
every retained initial clause.  Those identifiers are enough to recover a
small semantic witness for each row without materialising the 3.37-million
clause source:

* one of the four Ramsey base families;
* a seven-vertex root-free slice and a position in its conditioned cube list;
* a root-containing six-vertex slice and a projected-cube position; or
* one of the final 22 root/sort/bound clauses.

The optional full report also reconstructs the conditioned cube lists.  It
checks every blocker width, assigns six-orbit provenance, counts the smaller
block-stabilizer orbits touched by the core, and independently fingerprints
the ``F8 + core extras`` formula.  It invokes no SAT solver or proof checker
and writes no large artifact.
"""

from __future__ import annotations

import argparse
import bisect
import csv
import functools
import hashlib
import itertools
import json
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Iterator, Sequence

from . import certify_cover6_cube_motif_bridge as bridge
from . import exact_replay_cover6_d8 as replay
from . import master8_prefix_pilot as master


HERE = Path(__file__).resolve().parent
CORE_DIRECTORY = HERE / "master8_core"
CORE_CNF = CORE_DIRECTORY / "cover6_closed_master_d8_bounded13_core.cnf"
CORE_MAPPING = CORE_DIRECTORY / "core_clause_map.tsv"
CORE_MANIFEST = CORE_DIRECTORY / "MANIFEST.json"
REPORT_NAME = "MASTER8_CORE_TAXONOMY_V1.json"

CORE_CLAUSES = 6_152
BASE_CLAUSES = 717
ROOT_FREE_FIRST = BASE_CLAUSES + 1
ROOT_FREE_CLAUSES = 3_210_480
ROOT_FREE_LAST = ROOT_FREE_FIRST + ROOT_FREE_CLAUSES - 1
ROOT_CONTAINING_FIRST = ROOT_FREE_LAST + 1
ROOT_CONTAINING_CLAUSES = 156_240
ROOT_CONTAINING_LAST = ROOT_CONTAINING_FIRST + ROOT_CONTAINING_CLAUSES - 1
FINAL_FIRST = replay.SOURCE_CLAUSES + 1
FINAL_LAST = replay.SOURCE_CLAUSES + 22

# The dependency core retains these clauses, in this order, from the final 22.
# Prefix clause three is (14, -15), hence is implied by the retained unit -15.
CORE8_PREFIX_POSITIONS = (1, 2, 4, 5, 6, 7, 8)
CORE8_EXTRA_MASTER_IDS = (
    replay.SOURCE_CLAUSES + 12,
    replay.SOURCE_CLAUSES + 13,
    replay.SOURCE_CLAUSES + 15,
    replay.SOURCE_CLAUSES + 16,
    replay.SOURCE_CLAUSES + 17,
    replay.SOURCE_CLAUSES + 18,
    replay.SOURCE_CLAUSES + 19,
    replay.SOURCE_CLAUSES + 20,
)
CORE8_EXTRA_CLAUSES: tuple[replay.Clause, ...] = (
    master.PREFIX_CLAUSES[0],
    master.PREFIX_CLAUSES[1],
    *master.PREFIX_CLAUSES[3:],
    master.BOUND_CLAUSES[0],
)
CORE8_FORMULA_NAME = "cover6_closed_core8_d8_normalized.cnf"
CORE8_CLAUSES = replay.SOURCE_CLAUSES + len(CORE8_EXTRA_CLAUSES)
CORE8_EXPECTED_BYTES = 189_298_301
CORE8_EXPECTED_SHA256 = (
    "0133D40DC0458E7CD426F22DA08B525B4197467E539E4446AE94A38E84D7341E"
)
CORE8_EXPECTED_WIDTHS = {
    "1": 1,
    "2": 7,
    "3": 57,
    "6": 660,
    "10": 32_256,
    "11": 69_552,
    "12": 36_288,
    "13": 18_144,
    "15": 912_240,
    "16": 1_209_600,
    "17": 1_088_640,
}


class TaxonomyError(ValueError):
    """The tracked core or declarative Master8 layout changed."""


@dataclass(frozen=True)
class ClauseRange:
    first: int
    last: int
    family: str
    condition: int
    vertices: tuple[int, ...]
    templates_per_slice: int


@dataclass(frozen=True)
class ClauseLocation:
    family: str
    subtype: str
    condition: int | None = None
    vertices: tuple[int, ...] = ()
    template_position: int | None = None


@dataclass(frozen=True)
class CoreRow:
    core_id: int
    master_id: int
    clause_sha256: str
    clause: replay.Clause
    location: ClauseLocation

    @property
    def width(self) -> int:
        return len(self.clause)


def sha256_file(path: Path) -> tuple[str, int]:
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(block)
            size += len(block)
    return digest.hexdigest().upper(), size


def digest_lines(lines: Iterable[str]) -> str:
    return hashlib.sha256("".join(lines).encode("ascii")).hexdigest().upper()


def counter_json(counter: Counter[int]) -> dict[str, int]:
    return {str(key): counter[key] for key in sorted(counter)}


def span(values: Sequence[int]) -> list[int]:
    if not values:
        return []
    return [min(values), max(values)]


def interval_count(values: Iterable[int]) -> int:
    ordered = sorted(set(values))
    return sum(index == 0 or value != ordered[index - 1] + 1
               for index, value in enumerate(ordered))


@functools.cache
def declarative_ranges() -> tuple[tuple[ClauseRange, ...], tuple[ClauseRange, ...]]:
    root_free: list[ClauseRange] = []
    next_id = ROOT_FREE_FIRST
    for vertices in itertools.combinations(range(1, 12), 7):
        condition = sum(vertex <= replay.DEGREE for vertex in vertices)
        count = replay.BLOCK_COUNTS[condition]
        root_free.append(ClauseRange(
            next_id,
            next_id + count - 1,
            "root_free_blocker",
            condition,
            vertices,
            count,
        ))
        next_id += count
    if next_id - 1 != ROOT_FREE_LAST:
        raise TaxonomyError("root-free declarative range changed")

    root_containing: list[ClauseRange] = []
    next_id = ROOT_CONTAINING_FIRST
    for vertices in itertools.combinations(range(1, 12), 6):
        condition = sum(vertex <= replay.DEGREE for vertex in vertices)
        count = replay.LOCAL_COUNTS[condition]
        if count:
            root_containing.append(ClauseRange(
                next_id,
                next_id + count - 1,
                "root_containing_blocker",
                condition,
                vertices,
                count,
            ))
        next_id += count
    if next_id - 1 != ROOT_CONTAINING_LAST:
        raise TaxonomyError("root-containing declarative range changed")
    return tuple(root_free), tuple(root_containing)


def _range_location(master_id: int, ranges: Sequence[ClauseRange]) -> ClauseLocation:
    ends = [item.last for item in ranges]
    position = bisect.bisect_left(ends, master_id)
    if position == len(ranges):
        raise TaxonomyError(f"clause {master_id} is outside its declarative family")
    item = ranges[position]
    if master_id < item.first:
        raise TaxonomyError(f"clause {master_id} falls in a zero-size slice")
    return ClauseLocation(
        family=item.family,
        subtype=item.family,
        condition=item.condition,
        vertices=item.vertices,
        template_position=master_id - item.first + 1,
    )


def classify_master_id(master_id: int) -> ClauseLocation:
    if not 1 <= master_id <= FINAL_LAST:
        raise TaxonomyError(f"Master8 clause id out of range: {master_id}")
    if master_id <= 660:
        pair_index, polarity = divmod(master_id - 1, 2)
        vertices = tuple(itertools.islice(
            itertools.combinations(range(1, 12), 4), pair_index, pair_index + 1
        ))[0]
        subtype = "ramsey_k4_negative" if polarity == 0 else "ramsey_k4_positive"
        return ClauseLocation("base_ramsey", subtype, vertices=vertices)
    if master_id <= 716:
        position = master_id - 661
        vertices = tuple(itertools.islice(
            itertools.combinations(range(1, 9), 3), position, position + 1
        ))[0]
        return ClauseLocation("base_ramsey", "root_neighbour_triangle_negative", vertices=vertices)
    if master_id == 717:
        return ClauseLocation(
            "base_ramsey", "root_nonneighbour_triangle_positive", vertices=(9, 10, 11)
        )
    root_free, root_containing = declarative_ranges()
    if master_id <= ROOT_FREE_LAST:
        return _range_location(master_id, root_free)
    if master_id <= ROOT_CONTAINING_LAST:
        return _range_location(master_id, root_containing)

    final_position = master_id - replay.SOURCE_CLAUSES
    if final_position <= 11:
        return ClauseLocation("final_22", "root_unit", template_position=final_position)
    if final_position <= 19:
        return ClauseLocation(
            "final_22", "prefix_sort", template_position=final_position - 11
        )
    return ClauseLocation(
        "final_22", "arithmetic_bound", template_position=final_position - 19
    )


def _read_mapping(path: Path) -> list[tuple[int, int, str]]:
    with path.open("r", encoding="ascii", newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        if reader.fieldnames != ["core_clause_id", "master8_clause_id", "clause_sha256"]:
            raise TaxonomyError("unexpected core mapping header")
        result = []
        for expected, row in enumerate(reader, 1):
            core_id = int(row["core_clause_id"])
            master_id = int(row["master8_clause_id"])
            digest = row["clause_sha256"]
            if core_id != expected:
                raise TaxonomyError("core mapping identifiers are not consecutive")
            if len(digest) != 64 or digest.upper() != digest:
                raise TaxonomyError(f"malformed clause hash at core row {core_id}")
            result.append((core_id, master_id, digest))
    if len(result) != CORE_CLAUSES:
        raise TaxonomyError(f"core mapping has {len(result)} rows")
    if any(left[1] >= right[1] for left, right in zip(result, result[1:])):
        raise TaxonomyError("Master8 identifiers are not strictly increasing")
    return result


def _read_core_cnf(path: Path) -> list[tuple[replay.Clause, bytes]]:
    with path.open("rb") as stream:
        header = stream.readline()
        if header != b"p cnf 66 6152\n":
            raise TaxonomyError(f"unexpected core CNF header: {header!r}")
        result = []
        for line_number, raw in enumerate(stream, 2):
            try:
                fields = tuple(map(int, raw.split()))
            except ValueError as error:
                raise TaxonomyError(f"non-integer core CNF row {line_number}") from error
            if len(fields) < 2 or fields[-1] != 0 or 0 in fields[:-1]:
                raise TaxonomyError(f"malformed core CNF row {line_number}")
            clause = fields[:-1]
            if any(not 1 <= abs(literal) <= replay.GLOBAL_VARIABLES for literal in clause):
                raise TaxonomyError(f"literal out of range at core CNF row {line_number}")
            canonical = replay.clause_line(clause)
            if raw != canonical:
                raise TaxonomyError(f"non-canonical core CNF row {line_number}")
            result.append((clause, raw))
    if len(result) != CORE_CLAUSES:
        raise TaxonomyError(f"core CNF has {len(result)} clauses")
    return result


@functools.cache
def core_rows() -> tuple[CoreRow, ...]:
    mapping = _read_mapping(CORE_MAPPING)
    clauses = _read_core_cnf(CORE_CNF)
    rows = []
    for (core_id, master_id, expected_hash), (clause, raw) in zip(mapping, clauses):
        observed_hash = hashlib.sha256(raw).hexdigest().upper()
        if observed_hash != expected_hash:
            raise TaxonomyError(f"clause hash mismatch at core row {core_id}")
        rows.append(CoreRow(
            core_id,
            master_id,
            observed_hash,
            clause,
            classify_master_id(master_id),
        ))
    return tuple(rows)


def _section_summary(rows: Sequence[CoreRow], generated: int) -> dict[str, object]:
    return {
        "generated_clauses": generated,
        "retained_clauses": len(rows),
        "retained_fraction": f"{len(rows)}/{generated}",
        "core_id_span": span([row.core_id for row in rows]),
        "master8_id_span": span([row.master_id for row in rows]),
        "widths": counter_json(Counter(row.width for row in rows)),
        "selected_master_id_sha256": digest_lines(
            f"{row.master_id}\n" for row in rows
        ),
    }


def _position_summary(rows: Sequence[CoreRow]) -> dict[str, object]:
    positions = sorted({
        row.location.template_position for row in rows
        if row.location.template_position is not None
    })
    multiplicities = Counter(
        Counter(row.location.template_position for row in rows).values()
    )
    return {
        "distinct": len(positions),
        "span": span(positions),
        "intervals": interval_count(positions),
        "sha256": digest_lines(f"{position}\n" for position in positions),
        "occurrence_multiplicity_counts": counter_json(multiplicities),
    }


def _condition_summary(rows: Sequence[CoreRow], family: str, condition: int) -> dict[str, object]:
    selected = [row for row in rows if row.location.condition == condition]
    choose = 7 if family == "root_free_blocker" else 6
    generated_slices = sum(
        sum(vertex <= replay.DEGREE for vertex in vertices) == condition
        for vertices in itertools.combinations(range(1, 12), choose)
    )
    templates_per_slice = (
        replay.BLOCK_COUNTS[condition]
        if family == "root_free_blocker"
        else replay.LOCAL_COUNTS[condition]
    )
    slices = sorted({row.location.vertices for row in selected})
    second_slices = sorted(vertices for vertices in slices if 1 in vertices)
    slice_occupancy = Counter(
        Counter(row.location.vertices for row in selected).values()
    )
    witness_hash = digest_lines(
        f"{row.core_id}\t{row.master_id}\t{condition}\t"
        f"{','.join(map(str, row.location.vertices))}\t"
        f"{row.location.template_position}\t{row.width}\n"
        for row in selected
    )
    return {
        "condition": condition,
        "generated_slices": generated_slices,
        "templates_per_slice": templates_per_slice,
        "generated_clauses": generated_slices * templates_per_slice,
        "retained_clauses": len(selected),
        "retained_slices": len(slices),
        "retained_slices_with_second_center_vertex_1": len(second_slices),
        "retained_clauses_with_second_center_vertex_1": sum(
            1 for row in selected if 1 in row.location.vertices
        ),
        "widths": counter_json(Counter(row.width for row in selected)),
        "core_id_span": span([row.core_id for row in selected]),
        "master8_id_span": span([row.master_id for row in selected]),
        "template_positions": _position_summary(selected),
        "slice_occupancy_counts": counter_json(slice_occupancy),
        "selected_slice_sha256": digest_lines(
            f"{','.join(map(str, vertices))}\n" for vertices in slices
        ),
        "exact_location_witness_sha256": witness_hash,
    }


def _stabilizer_owner(
    cubes: Sequence[replay.Cube], order: int, condition: int
) -> tuple[dict[replay.Cube, int], tuple[replay.Cube, ...]]:
    selected = set(cubes)
    remaining = set(selected)
    permutations = bridge.block_stabilizer(order, condition)
    owner: dict[replay.Cube, int] = {}
    representatives = []
    while remaining:
        representative = min(remaining, key=lambda cube: (cube[1], cube[0]))
        orbit = {
            bridge.transform_cube_order(representative, permutation, order)
            for permutation in permutations
        }
        if not orbit <= selected:
            raise TaxonomyError("conditioned cube family is not stabilizer-closed")
        orbit_index = len(representatives)
        representatives.append(representative)
        for cube in orbit:
            owner[cube] = orbit_index
        remaining -= orbit
    return owner, tuple(representatives)


def _enrich_conditioned(
    rows: Sequence[CoreRow], family: str, summaries: list[dict[str, object]]
) -> None:
    _cube_orbits, cube_owner = bridge.cube_data()
    if family == "root_free_blocker":
        conditioned = replay.block_conditioned_cubes()
        order = 7
    else:
        conditioned = replay.local_conditioned_cubes()
        order = 6

    for summary in summaries:
        condition = int(summary["condition"])
        selected_rows = [row for row in rows if row.location.condition == condition]
        positions = sorted({int(row.location.template_position) for row in selected_rows})
        templates = [conditioned[condition][position - 1] for position in positions]
        stabilizer_owner, representatives = _stabilizer_owner(
            conditioned[condition], order, condition
        )
        touched = sorted({stabilizer_owner[cube] for cube in templates})

        if any(row.width != conditioned[condition][int(row.location.template_position) - 1][1].bit_count()
               for row in selected_rows):
            raise TaxonomyError("blocker width differs from conditioned cube width")

        if family == "root_free_blocker":
            provenance_of = lambda cube: cube_owner[cube]
        else:
            lifts = bridge.root_containing_lifts(cube_owner, condition)
            if any(len(lifts[cube]) != 1 for cube in conditioned[condition]):
                raise TaxonomyError("projected cube does not have a unique full lift")
            provenance_of = lambda cube: cube_owner[lifts[cube][0]]

        occurrence_provenance = Counter(
            provenance_of(conditioned[condition][int(row.location.template_position) - 1])
            for row in selected_rows
        )
        template_provenance = Counter(provenance_of(cube) for cube in templates)
        summary["cube_compression"] = {
            "distinct_conditioned_templates": len(templates),
            "distinct_template_widths": counter_json(
                Counter(cube[1].bit_count() for cube in templates)
            ),
            "six_s7_representative_occurrence_counts": {
                str(index): occurrence_provenance.get(index, 0) for index in range(6)
            },
            "six_s7_representative_distinct_template_counts": {
                str(index): template_provenance.get(index, 0) for index in range(6)
            },
            "conditioned_stabilizer_orbits_total": len(representatives),
            "conditioned_stabilizer_orbits_touched": len(touched),
            "touched_orbit_index_sha256": digest_lines(
                f"{index}\n" for index in touched
            ),
            "all_stabilizer_representatives_sha256": replay.cubes_digest(representatives),
        }


def audit_core8_extras() -> dict[str, object]:
    if len(CORE8_EXTRA_MASTER_IDS) != 8 or len(CORE8_EXTRA_CLAUSES) != 8:
        raise TaxonomyError("core8 extra-clause count changed")
    if CORE8_EXTRA_CLAUSES != (
        master.PREFIX_CLAUSES[0], master.PREFIX_CLAUSES[1],
        *master.PREFIX_CLAUSES[3:], master.BOUND_CLAUSES[0]
    ):
        raise TaxonomyError("core8 extra clauses changed")

    models = master.assignments(CORE8_EXTRA_CLAUSES)
    pairs = tuple(sorted(master.assignment_pair(model) for model in models))
    expected_pairs = tuple((p, q) for p in range(4) for q in range(4))
    if pairs != expected_pairs:
        raise TaxonomyError("core8 extras do not encode exactly 0<=p,q<=3 prefixes")
    if any(not master.is_prefix(tuple(model[v] for v in master.LEFT_VARIABLES))
           or not master.is_prefix(tuple(model[v] for v in master.RIGHT_VARIABLES))
           for model in models):
        raise TaxonomyError("core8 extras admit a non-prefix assignment")
    missing = master.PREFIX_CLAUSES[2]
    if missing != (14, -15) or any(
        not master.clause_satisfied(missing, model) for model in models
    ):
        raise TaxonomyError("the omitted prefix clause is not implied by -15")

    return {
        "status": "PASS_EXACT_CORE8_FINITE_NORMALIZATION",
        "retained_prefix_positions": list(CORE8_PREFIX_POSITIONS),
        "omitted_prefix_position": 3,
        "omitted_prefix_clause": list(missing),
        "omitted_prefix_implied_by_retained_unit_minus_15": True,
        "models_over_variables_12_to_21": len(models),
        "model_pairs": [list(pair) for pair in pairs],
        "exact_pair_set": "0 <= p <= 3 and 0 <= q <= 3",
        "cross_lower_bound_p_plus_q_ge_two_used": False,
        "thirteen_case_partition_used": False,
    }


def fingerprint_core8() -> dict[str, object]:
    clauses: Iterator[replay.Clause] = itertools.chain(
        replay.expected_source_clauses(), CORE8_EXTRA_CLAUSES
    )
    observed = master.stream_formula(clauses, CORE8_CLAUSES)
    expected = {
        "variables": replay.GLOBAL_VARIABLES,
        "clauses": CORE8_CLAUSES,
        "bytes": CORE8_EXPECTED_BYTES,
        "sha256": CORE8_EXPECTED_SHA256,
        "widths": CORE8_EXPECTED_WIDTHS,
    }
    if observed != expected:
        raise TaxonomyError(f"core8 formula fingerprint changed: {observed}")
    return observed


def _base_report(rows: Sequence[CoreRow]) -> dict[str, object]:
    subtypes = []
    for subtype in (
        "ramsey_k4_negative",
        "ramsey_k4_positive",
        "root_neighbour_triangle_negative",
        "root_nonneighbour_triangle_positive",
    ):
        selected = [row for row in rows if row.location.subtype == subtype]
        subtypes.append({
            "name": subtype,
            "retained_clauses": len(selected),
            "widths": counter_json(Counter(row.width for row in selected)),
            "master8_id_span": span([row.master_id for row in selected]),
            "vertex_slice_sha256": digest_lines(
                f"{','.join(map(str, row.location.vertices))}\n" for row in selected
            ),
        })
    result = _section_summary(rows, BASE_CLAUSES)
    result.update({
        "master8_range": [1, BASE_CLAUSES],
        "subfamilies": subtypes,
        "distinct_k4_vertex_slices": len({
            row.location.vertices for row in rows if row.location.subtype.startswith("ramsey_k4")
        }),
    })
    return result


def _final_report(rows: Sequence[CoreRow]) -> dict[str, object]:
    all_final = master.ROOT_UNITS + master.PREFIX_CLAUSES + master.BOUND_CLAUSES
    if len(all_final) != 22:
        raise TaxonomyError("Master8 final-clause block changed")
    retained_by_master = {row.master_id: row for row in rows}
    details = []
    for position, clause in enumerate(all_final, 1):
        master_id = replay.SOURCE_CLAUSES + position
        if position <= 11:
            category, local_position = "root_unit", position
        elif position <= 19:
            category, local_position = "prefix_sort", position - 11
        else:
            category, local_position = "arithmetic_bound", position - 19
        row = retained_by_master.get(master_id)
        details.append({
            "final_position": position,
            "master8_clause_id": master_id,
            "category": category,
            "category_position": local_position,
            "clause": list(clause),
            "retained": row is not None,
            "core_clause_id": row.core_id if row else None,
        })
        if row is not None and row.clause != clause:
            raise TaxonomyError(f"final clause content mismatch at position {position}")
    retained_ids = tuple(item["master8_clause_id"] for item in details if item["retained"])
    if retained_ids != CORE8_EXTRA_MASTER_IDS:
        raise TaxonomyError(f"retained final clauses changed: {retained_ids}")
    result = _section_summary(rows, 22)
    result.update({
        "master8_range": [FINAL_FIRST, FINAL_LAST],
        "retained_of_22": 8,
        "root_units_retained": 0,
        "prefix_sort_clauses_retained": 7,
        "arithmetic_bounds_retained": 1,
        "details": details,
    })
    return result


def build_report(*, full: bool) -> dict[str, object]:
    rows = core_rows()
    manifest = json.loads(CORE_MANIFEST.read_text(encoding="utf-8"))
    mapping_hash, mapping_bytes = sha256_file(CORE_MAPPING)
    cnf_hash, cnf_bytes = sha256_file(CORE_CNF)
    if (mapping_hash, mapping_bytes) != (
        manifest["artifacts"]["initial_clause_mapping"]["sha256"],
        manifest["artifacts"]["initial_clause_mapping"]["bytes"],
    ):
        raise TaxonomyError("mapping identity differs from the replay manifest")
    if (cnf_hash, cnf_bytes) != (
        manifest["artifacts"]["cnf"]["sha256"],
        manifest["artifacts"]["cnf"]["bytes"],
    ):
        raise TaxonomyError("core CNF identity differs from the replay manifest")

    by_family: dict[str, list[CoreRow]] = defaultdict(list)
    for row in rows:
        by_family[row.location.family].append(row)
    expected_counts = {
        "base_ramsey": 221,
        "root_free_blocker": 3_514,
        "root_containing_blocker": 2_409,
        "final_22": 8,
    }
    if {key: len(value) for key, value in by_family.items()} != expected_counts:
        raise TaxonomyError("core family counts changed")

    root_free_conditions = [
        _condition_summary(by_family["root_free_blocker"], "root_free_blocker", condition)
        for condition in (4, 5, 6, 7)
    ]
    root_containing_conditions = [
        _condition_summary(
            by_family["root_containing_blocker"], "root_containing_blocker", condition
        )
        for condition in (3, 4, 5, 6)
    ]
    if full:
        _enrich_conditioned(
            by_family["root_free_blocker"], "root_free_blocker", root_free_conditions
        )
        _enrich_conditioned(
            by_family["root_containing_blocker"],
            "root_containing_blocker",
            root_containing_conditions,
        )

    root_free_report = _section_summary(
        by_family["root_free_blocker"], ROOT_FREE_CLAUSES
    )
    root_free_report.update({
        "master8_range": [ROOT_FREE_FIRST, ROOT_FREE_LAST],
        "slice_order": "lexicographic 7-subsets of vertices 1..11",
        "template_order": "(fixed.bit_count, fixed, ones)",
        "conditions": root_free_conditions,
    })
    root_containing_report = _section_summary(
        by_family["root_containing_blocker"], ROOT_CONTAINING_CLAUSES
    )
    root_containing_report.update({
        "master8_range": [ROOT_CONTAINING_FIRST, ROOT_CONTAINING_LAST],
        "slice_order": "lexicographic 6-subsets of vertices 1..11; root 0 is implicit",
        "template_order": "(fixed.bit_count, fixed, ones) after root-edge projection",
        "conditions": root_containing_conditions,
    })

    taxonomy_digest = digest_lines(
        f"{row.core_id}\t{row.master_id}\t{row.location.family}\t"
        f"{row.location.subtype}\t{row.location.condition}\t"
        f"{','.join(map(str, row.location.vertices))}\t"
        f"{row.location.template_position}\t{row.width}\t{row.clause_sha256}\n"
        for row in rows
    )
    core_widths = counter_json(Counter(row.width for row in rows))
    if sum(core_widths.values()) != CORE_CLAUSES:
        raise TaxonomyError("core width total changed")
    root_variable_occurrences = sum(
        1 for row in rows for literal in row.clause if abs(literal) <= 11
    )
    if root_variable_occurrences:
        raise TaxonomyError("the dependency core unexpectedly uses root variables 1..11")

    core8_fingerprint = (
        fingerprint_core8()
        if full
        else {
            "variables": replay.GLOBAL_VARIABLES,
            "clauses": CORE8_CLAUSES,
            "bytes": CORE8_EXPECTED_BYTES,
            "sha256": CORE8_EXPECTED_SHA256,
            "widths": CORE8_EXPECTED_WIDTHS,
        }
    )
    finite = audit_core8_extras()

    distinct_templates = sum(
        int(condition["template_positions"]["distinct"])
        for condition in root_free_conditions + root_containing_conditions
    )
    touched_orbits = None
    if full:
        touched_orbits = sum(
            int(condition["cube_compression"]["conditioned_stabilizer_orbits_touched"])
            for condition in root_free_conditions + root_containing_conditions
        )

    return {
        "schema_version": 1,
        "status": "PASS_EXACT_MASTER8_CORE_TAXONOMY",
        "inputs": {
            "master8": {
                "variables": replay.GLOBAL_VARIABLES,
                "clauses": FINAL_LAST,
                "sha256": master.BOUNDED_EXPECTED_SHA256,
            },
            "core_cnf": {
                "clauses": CORE_CLAUSES,
                "bytes": cnf_bytes,
                "sha256": cnf_hash,
            },
            "core_clause_mapping": {
                "rows": CORE_CLAUSES,
                "bytes": mapping_bytes,
                "sha256": mapping_hash,
            },
        },
        "declarative_layout": {
            "base_ramsey": [1, BASE_CLAUSES],
            "root_free_blockers": [ROOT_FREE_FIRST, ROOT_FREE_LAST],
            "root_containing_blockers": [ROOT_CONTAINING_FIRST, ROOT_CONTAINING_LAST],
            "final_22": [FINAL_FIRST, FINAL_LAST],
            "total_clauses": FINAL_LAST,
        },
        "core": {
            "clauses": CORE_CLAUSES,
            "widths": core_widths,
            "root_variable_1_to_11_occurrences": root_variable_occurrences,
            "exact_taxonomy_row_sha256": taxonomy_digest,
        },
        "sections": {
            "base_ramsey": _base_report(by_family["base_ramsey"]),
            "root_free_blockers": root_free_report,
            "root_containing_blockers": root_containing_report,
            "final_22": _final_report(by_family["final_22"]),
        },
        "compression": {
            "conditioned_blocker_instances_retained": (
                len(by_family["root_free_blocker"])
                + len(by_family["root_containing_blocker"])
            ),
            "distinct_conditioned_template_positions": distinct_templates,
            "conditioned_stabilizer_orbits_touched": touched_orbits,
            "semantic_orbit_roots_available": 6,
            "lean_strategy": (
                "classify by arithmetic Master8 index; reuse the six proved S7 cube roots "
                "for root-free blockers and the existing equivariant projected-lift bridge "
                "for root-containing blockers"
            ),
            "warning": (
                "the core-selected templates need not be whole stabilizer orbits; exact "
                "slice/template-position witnesses remain necessary for clause equality"
            ),
        },
        "normalized_core8_variant": {
            "name": CORE8_FORMULA_NAME,
            "construction": "F8 followed by the eight final clauses used by the LRAT core",
            "extra_master8_clause_ids": list(CORE8_EXTRA_MASTER_IDS),
            "extra_clauses": [list(clause) for clause in CORE8_EXTRA_CLAUSES],
            "formula": core8_fingerprint,
            "finite_normalization": finite,
            "root_units_used": False,
            "reason_root_units_are_absent": (
                "F8 and the eight retained extras mention only DIMACS variables 12..66; "
                "the root block is supplied semantically by rootSort_exact_eight"
            ),
            "existing_lean_route": {
                "prefix_sort": ["secondSort_left_edge", "secondSort_right_edge"],
                "unit_minus_15": "pValue_le_three plus twoCenter_second_left at position 3",
                "transport": [
                    "twoCenter_isRamseyFree_iff",
                    "twoCenter_inducedMotifOccurrence_iff",
                ],
                "qValue_le_three_needed": False,
                "positive_degree_lower_bound_needed": False,
                "thirteen_cases_needed": False,
            },
            "formal_status": (
                "the finite extras, the lazy Lean F8 generator, and the exact core selection "
                "are now formalized; a full theorem still needs the graph-level semantic "
                "satisfaction proof for the four clause families"
            ),
        },
        "scope": (
            "Exact syntactic taxonomy of the replayed dependency core plus deterministic "
            "cube-provenance and formula-fingerprint checks. The separate Lean indexed-source "
            "module now defines and refutes this formula; this report does not itself prove "
            "the graph-to-formula semantic bridge."
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command", choices=("summary", "report", "verify-tracked"), nargs="?", default="summary"
    )
    parser.add_argument(
        "--full", action="store_true",
        help="reconstruct conditioned cubes/orbits and the 189 MB formula fingerprint",
    )
    args = parser.parse_args()
    full = args.full or args.command in ("report", "verify-tracked")
    report = build_report(full=full)
    if args.command == "verify-tracked":
        tracked = json.loads((HERE / REPORT_NAME).read_text(encoding="utf-8"))
        if report != tracked:
            raise TaxonomyError("generated taxonomy differs from tracked report")
        print(json.dumps({"status": "PASS", "report": REPORT_NAME}, indent=2))
    else:
        print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
