#!/usr/bin/env python3
"""Frozen registry for the seven not-yet-certified R34 order-seven leaves.

This module is deliberately data-only plus cheap local consistency checks.  It
does not read ``S:``, materialize a large formula, or invoke a solver.  The
already-certified ``F`GOW`` route and the direct-motif oracle ``FG`Xo`` remain
listed as excluded sentinels so a parameterized caller cannot silently reuse
or overwrite either path.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass
from pathlib import Path

from . import materialize_cover6_d7_r34_catalogue_icnf as catalogue


HERE = Path(__file__).resolve().parent
PILOT_REPORT = HERE / "MASTER7_R34_CATALOGUE9_PILOT_V1.json"
PILOT_REPORT_BYTES = 7_851
PILOT_REPORT_SHA256 = (
    "205E5F05132D7EDDA4C8ED14A8773CA12EB7BAEC2CB79EEC3391DD855071C323"
)

SOURCE_VARIABLES = 66
SOURCE_CLAUSES = 4_312_419
TARGET_CLAUSES = 4_312_440
TARGET_LINES = 4_312_441
TARGET_HEADER = b"p cnf 66 4312440\n"
UNIT_COUNT = 21


class R34LeafRegistryError(ValueError):
    """Raised at the first frozen-registry or selection mismatch."""


@dataclass(frozen=True)
class LeafSpec:
    slug: str
    record: str
    source_catalogue_index_zero_based: int
    incremental_position_one_based: int
    degree_sequence: tuple[int, ...]
    cube: tuple[int, ...]
    unit_payload_bytes: int
    unit_payload_sha256: str
    target_bytes: int
    target_sha256: str
    pilot_conflicts: int
    pilot_elapsed_seconds: float
    pilot_failed_assumptions: int
    disposition: str

    @property
    def target_name(self) -> str:
        return (
            f"cover6_closed_f7_r34_i{self.incremental_position_one_based}_"
            f"{self.slug}.cnf"
        )

    @property
    def artifact_stem(self) -> str:
        return self.target_name.removesuffix(".cnf") + "_c25k"


TICK = chr(96)

# Order is the exact incremental pilot order.  Hashes were reconstructed in a
# single local streaming pass from the tracked F7 primitives, not from S:.
ALL_LEAVES = (
    LeafSpec(
        "FGgraveXo", "FG" + TICK + "Xo", 1, 1,
        (1, 2, 2, 2, 3, 3, 3),
        (-12, -13, -14, 15, -16, -17, 22, -23, -24, 25, -26,
         -31, -32, -33, 34, -39, 40, 41, 46, 47, -52),
        118, "0CABC070A13D973BB742DA67AFB59F9E1EF8DA09BBBD0B7416653314ED8686C7",
        246_507_633, "216B57473C60D474212FDE809B0B278BE0521366C9D37198A3E75856649B4EF0",
        0, 0.172, 14, "EXCLUDED_DIRECT_MOTIF_ORACLE",
    ),
    LeafSpec(
        "FCUj_", "FCUj_", 0, 2,
        (2, 2, 2, 3, 3, 3, 3),
        (-12, -13, 14, -15, 16, -17, -22, -23, 24, -25, 26,
         -31, -32, 33, 34, 39, -40, 41, 46, -47, -52),
        117, "4F3E6D5178D9F773B3C6F0F0665C160158639446133BF57264284F638249C4B5",
        246_507_632, "B2685E5462A82045AA4805E1E92BF345061E4E04AC7F640EA89DA7E10501A32A",
        507, 0.938, 15, "ACTIONABLE",
    ),
    LeafSpec(
        "FKgraveXo", "FK" + TICK + "Xo", 2, 3,
        (2, 2, 2, 3, 3, 3, 3),
        (-12, -13, 14, 15, -16, -17, 22, -23, -24, 25, -26,
         -31, -32, -33, 34, -39, 40, 41, 46, 47, -52),
        117, "583443CB7CEA48EB1180C890CFC206ACF2FDF17A530EDC786B8A698C67930CAB",
        246_507_632, "A595E2B30BE05065089522BB74873C746B5AEEBD80E99E90ABF9D389D62BF9D1",
        2_092, 2.469, 15, "ACTIONABLE",
    ),
    LeafSpec(
        "F_GZ_", "F_GZ_", 3, 4,
        (1, 2, 2, 2, 2, 2, 3),
        (12, -13, -14, -15, -16, -17, -22, -23, -24, -25, 26,
         -31, 32, -33, 34, -39, 40, 41, 46, -47, -52),
        119, "EA060CD989B1A66D6D4314EDE5C4D01B61F5FA7C3B304C9E848EDACD2EDE581B",
        246_507_634, "F27AAC37CDC053B0E332CC53867D3A43C5A81400ACB1D3B8198EF30EBE690A58",
        1_604, 1.547, 16, "ACTIONABLE",
    ),
    LeafSpec(
        "FgraveAZO", "F" + TICK + "AZO", 4, 5,
        (2, 2, 2, 2, 2, 3, 3),
        (12, -13, -14, -15, 16, -17, -22, -23, -24, -25, 26,
         31, -32, -33, 34, -39, 40, -41, 46, 47, -52),
        118, "3006CCF80E0A7E6E1DD7FFED7D7C1BEC601FB08E83CF17D54F9D8F8541EA6527",
        246_507_633, "BB8923D357D4BAA249D6E64DBE553267D1A6CB82D09CABFA5A29D853974AC26D",
        808, 2.516, 14, "ACTIONABLE",
    ),
    LeafSpec(
        "FgraveGOW", "F" + TICK + "GOW", 5, 6,
        (1, 1, 2, 2, 2, 2, 2),
        (12, -13, -14, -15, -16, -17, -22, -23, -24, -25, -26,
         31, 32, -33, -34, -39, 40, -41, -46, 47, 52),
        120, "4C2D8603575965D0CB08E3CDC7AC7AD463CA369D4EDDB645E565599A0F13373F",
        246_507_635, "78D066E03B1F55FACBF8839BCC409E0D45BABF93FA6D266628BB526D2F5E5971",
        3_944, 5.781, 19, "EXCLUDED_FROZEN_CERTIFIED_PATH",
    ),
    LeafSpec(
        "FoDPO", "FoDPO", 6, 7,
        (2, 2, 2, 2, 2, 2, 2),
        (12, 13, -14, -15, -16, -17, -22, -23, -24, 25, -26,
         -31, -32, -33, 34, 39, 40, -41, -46, 47, -52),
        119, "3CAB9BA8B69E6DD1B96B048060D10796832A5F6D87B2D2EEDAB1D199718D8C5C",
        246_507_634, "D5B114A896883A31551FC668B6F7167676A86EFCB3FCF8CC33678B81D57E0331",
        3_474, 4.297, 17, "ACTIONABLE_FIRST",
    ),
    LeafSpec(
        "FoDPW", "FoDPW", 7, 8,
        (2, 2, 2, 2, 2, 3, 3),
        (12, 13, -14, -15, -16, -17, -22, -23, -24, 25, -26,
         -31, -32, -33, 34, 39, 40, -41, -46, 47, 52),
        118, "6681672FCC1A21709EA612FA61BF659D0DC7422057119E75B1A13DC7151B0448",
        246_507_633, "225DFD79BBFFD90D2107D46521669F2E17B8807BCF77516E1D30E91C61DC6EF0",
        1_280, 1.047, 15, "ACTIONABLE",
    ),
    LeafSpec(
        "FqOxo", "FqOxo", 8, 9,
        (2, 3, 3, 3, 3, 3, 3),
        (12, 13, -14, -15, -16, -17, -22, 23, 24, -25, -26,
         -31, -32, 33, 34, -39, 40, 41, 46, 47, -52),
        116, "69B7BFB6A52D07FC6FCC517BDF11BDE9165115BA77E5678326B4B3045B0FCA00",
        246_507_631, "08057558CCF137570B3CE0634BAA2D9D6ED32BF2866C8C68BB40971EA71A2CE3",
        3_184, 4.375, 11, "ACTIONABLE",
    ),
)

LEAF_BY_SLUG = {leaf.slug: leaf for leaf in ALL_LEAVES}
ACTIONABLE_LEAVES = tuple(
    leaf for leaf in ALL_LEAVES if leaf.disposition.startswith("ACTIONABLE")
)
ACTIONABLE_SLUGS = tuple(leaf.slug for leaf in ACTIONABLE_LEAVES)
FIRST_LEAF_SLUG = "FoDPO"
FIRST_LEAF_RATIONALE = (
    "explicit next-leaf choice after the frozen FgraveGOW path; its 3,474-conflict "
    "catalogue pilot is nontrivial yet comfortably below the 25,000-conflict cap"
)


def unit_payload(spec: LeafSpec) -> bytes:
    return b"".join(f"{literal} 0\n".encode("ascii") for literal in spec.cube)


def select_actionable(slug: str) -> LeafSpec:
    spec = LEAF_BY_SLUG.get(slug)
    if spec is None:
        raise R34LeafRegistryError(
            f"unknown leaf {slug!r}; choose one of {', '.join(ACTIONABLE_SLUGS)}"
        )
    if not spec.disposition.startswith("ACTIONABLE"):
        raise R34LeafRegistryError(
            f"leaf {slug} is not selectable: {spec.disposition}"
        )
    return spec


def _file_identity(path: Path) -> tuple[int, str]:
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            size += len(block)
            digest.update(block)
    return size, digest.hexdigest().upper()


def audit_registry(*, verify_pilot_report: bool = True) -> dict[str, object]:
    if len(ALL_LEAVES) != 9 or len(ACTIONABLE_LEAVES) != 7:
        raise R34LeafRegistryError("expected nine total and seven actionable leaves")
    if len(LEAF_BY_SLUG) != len(ALL_LEAVES):
        raise R34LeafRegistryError("leaf slugs are not unique")
    if tuple(leaf.record for leaf in ALL_LEAVES) != catalogue.ORDERED_R34_RECORDS:
        raise R34LeafRegistryError("registry order differs from the frozen catalogue")
    if LEAF_BY_SLUG[FIRST_LEAF_SLUG].pilot_conflicts != 3_474:
        raise R34LeafRegistryError("FoDPO pilot anchor changed")

    expected_variables = set(catalogue.H_VARIABLES)
    for spec in ALL_LEAVES:
        if catalogue.SOURCE_R34_RECORDS[spec.source_catalogue_index_zero_based] != spec.record:
            raise R34LeafRegistryError(f"source index changed for {spec.slug}")
        if catalogue.ORDERED_R34_RECORDS[spec.incremental_position_one_based - 1] != spec.record:
            raise R34LeafRegistryError(f"incremental position changed for {spec.slug}")
        if catalogue.cube_for_record(spec.record) != spec.cube:
            raise R34LeafRegistryError(f"cube changed for {spec.slug}")
        if catalogue.degree_sequence(catalogue.graph6_mask(spec.record)) != spec.degree_sequence:
            raise R34LeafRegistryError(f"degree sequence changed for {spec.slug}")
        if len(spec.cube) != UNIT_COUNT or {abs(x) for x in spec.cube} != expected_variables:
            raise R34LeafRegistryError(f"invalid exact K7 assignment for {spec.slug}")
        payload = unit_payload(spec)
        observed = (len(payload), hashlib.sha256(payload).hexdigest().upper())
        expected = (spec.unit_payload_bytes, spec.unit_payload_sha256)
        if observed != expected:
            raise R34LeafRegistryError(
                f"unit payload identity changed for {spec.slug}: {observed} != {expected}"
            )

    pilot_identity: dict[str, object] | None = None
    if verify_pilot_report:
        size, digest = _file_identity(PILOT_REPORT)
        if (size, digest) != (PILOT_REPORT_BYTES, PILOT_REPORT_SHA256):
            raise R34LeafRegistryError("catalogue pilot report identity changed")
        report = json.loads(PILOT_REPORT.read_text(encoding="utf-8"))
        rows = report.get("cube_order") if isinstance(report, dict) else None
        if not isinstance(rows, list) or len(rows) != len(ALL_LEAVES):
            raise R34LeafRegistryError("catalogue pilot rows are malformed")
        for spec, row in zip(ALL_LEAVES, rows, strict=True):
            checks = (
                (row.get("record"), spec.record),
                (row.get("index_one_based"), spec.incremental_position_one_based),
                (row.get("cube_conflicts"), spec.pilot_conflicts),
                (row.get("elapsed_seconds"), spec.pilot_elapsed_seconds),
                (row.get("failed_assumptions"), spec.pilot_failed_assumptions),
                (row.get("status"), "UNSATISFIABLE"),
            )
            if any(observed != expected for observed, expected in checks):
                raise R34LeafRegistryError(f"pilot row changed for {spec.slug}")
        pilot_identity = {
            "name": PILOT_REPORT.name,
            "bytes": size,
            "sha256": digest,
            "proof_level": 2,
        }

    return {
        "status": "PASS_FROZEN_R34_LEAF_REGISTRY_NO_S_NO_SOLVER",
        "first_leaf": FIRST_LEAF_SLUG,
        "first_leaf_rationale": FIRST_LEAF_RATIONALE,
        "actionable_slugs": list(ACTIONABLE_SLUGS),
        "excluded": {
            "FGgraveXo": "direct motif oracle",
            "FgraveGOW": "existing certified path preserved bit-for-bit",
        },
        "leaves": [asdict(leaf) | {"target_name": leaf.target_name} for leaf in ALL_LEAVES],
        "pilot_report": pilot_identity,
    }


if __name__ == "__main__":
    print(json.dumps(audit_registry(), indent=2, sort_keys=True))
