"""Check the published extremal R(4,5,20) record and the d20,c10 consequence.

The finite classification facts ``E(4,5,20) = 100`` and uniqueness of its
100-edge isomorphism class are trusted inputs. This verifier checks the unique
published graph, then checks the elementary minimum-anchor deduction and the
resulting branch-count arithmetic.  It does not certify the exhaustiveness of
the external classification.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence

from ramsey import (
    complement_graph,
    count_cliques,
    decode_graph6,
    graph_edge_count,
    validate_graph,
)


HERE = Path(__file__).resolve().parent
DEFAULT_GRAPH_PATH = HERE / "r4520.100.g6"

OFFICIAL_ARCHIVE_URL = "https://users.cecs.anu.edu.au/~bdm/data/r45extreme.tar.gz"
OFFICIAL_ARCHIVE_SIZE = 90_599_728
OFFICIAL_ARCHIVE_SHA256 = (
    "9cfac9dbd1c209cfa342e5d5424df2a7a3fbb008ca00bf0a992e5bbe72f925b6"
)
OFFICIAL_ARCHIVE_MEMBER = "r45extreme/r4520.100.g6"
OFFICIAL_GRAPH6 = r"SznZXmZR\HxJSjYEbWyDZ`XsuI]``lAb["
OFFICIAL_GRAPH_BYTES = OFFICIAL_GRAPH6.encode("ascii") + b"\n"
OFFICIAL_GRAPH_SHA256 = (
    "d1d1ff46bd5d153b51d7da094f6bf459bceaefda65eb4941ead0bb9b09c897cd"
)

# Published classification inputs.  The local record check below authenticates
# their unique representative but does not independently prove completeness.
TRUSTED_R45_20_MAXIMUM_EDGES = 100
TRUSTED_R45_20_MAXIMUM_EDGE_CLASS_COUNT = 1

EXPECTED_ORDER = 20
EXPECTED_DEGREES = (9, 9) + (10,) * 16 + (11, 11)
MINIMUM_ANCHOR_CODEGREE = 10

EXPECTED_R35_COUNTS = {
    0: 1,
    1: 1,
    2: 2,
    3: 3,
    4: 7,
    5: 13,
    6: 32,
    7: 71,
    8: 179,
    9: 290,
    10: 313,
}
EXPECTED_K43_TIGHT_BEFORE = 1_509
EXPECTED_K43_TIGHT_AFTER = 1_196
EXPECTED_K45_TIGHT_BEFORE = 1_815
EXPECTED_K45_TIGHT_AFTER = 1_502


class VerificationError(RuntimeError):
    """Raised when a checked byte-level or mathematical invariant fails."""


@dataclass(frozen=True)
class ExtremalGraphFacts:
    path: str
    byte_count: int
    sha256: str
    graph6: str
    order: int
    edge_count: int
    degrees: tuple[int, ...]
    degree_multiplicities: tuple[tuple[int, int], ...]
    red_k4_count: int
    independent_5_count: int


@dataclass(frozen=True)
class MinimumAnchorFacts:
    anchor_codegree: int
    handshake_edge_lower_bound: int
    trusted_extremal_edge_upper_bound: int
    trusted_extremal_class_count: int
    unique_extremal_graph_is_regular: bool
    d20_c10_minimum_anchor_empty: bool


@dataclass(frozen=True)
class BranchCountFacts:
    r35_counts: tuple[tuple[int, int], ...]
    eliminated_d20_c10_types: int
    k43_before: int
    k43_after: int
    k45_before: int
    k45_after: int


@dataclass(frozen=True)
class VerificationReport:
    official_graph: ExtremalGraphFacts
    minimum_anchor: MinimumAnchorFacts
    branch_counts: BranchCountFacts
    classification_scope: str


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


def verify_extremal_graph_bytes(
    payload: bytes, *, source: str = "<memory>"
) -> ExtremalGraphFacts:
    """Authenticate and inspect the exact published ``r4520.100.g6`` bytes."""

    digest = hashlib.sha256(payload).hexdigest()
    _require(len(payload) == 34, f"{source}: expected 34 bytes, got {len(payload)}")
    _require(
        digest == OFFICIAL_GRAPH_SHA256,
        f"{source}: SHA-256 mismatch: expected {OFFICIAL_GRAPH_SHA256}, got {digest}",
    )
    _require(payload == OFFICIAL_GRAPH_BYTES, f"{source}: unexpected graph6 bytes")

    try:
        text = payload.decode("ascii")
    except UnicodeDecodeError as error:
        raise VerificationError(f"{source}: graph6 data is not ASCII") from error
    records = text.splitlines()
    _require(len(records) == 1, f"{source}: expected one graph6 record")
    _require(records[0] == OFFICIAL_GRAPH6, f"{source}: unexpected graph6 record")

    graph = decode_graph6(records[0])
    validate_graph(graph)
    degrees = tuple(sorted(row.bit_count() for row in graph))
    edge_count = graph_edge_count(graph)
    red_k4_count = count_cliques(graph, 4)
    independent_5_count = count_cliques(complement_graph(graph), 5)

    _require(len(graph) == EXPECTED_ORDER, f"{source}: expected order 20")
    _require(edge_count == 100, f"{source}: expected 100 edges, got {edge_count}")
    _require(
        degrees == EXPECTED_DEGREES,
        f"{source}: unexpected degree sequence {degrees}",
    )
    _require(red_k4_count == 0, f"{source}: graph contains a K4")
    _require(
        independent_5_count == 0,
        f"{source}: graph contains an independent set of order 5",
    )

    return ExtremalGraphFacts(
        path=source,
        byte_count=len(payload),
        sha256=digest,
        graph6=records[0],
        order=len(graph),
        edge_count=edge_count,
        degrees=degrees,
        degree_multiplicities=tuple(sorted(Counter(degrees).items())),
        red_k4_count=red_k4_count,
        independent_5_count=independent_5_count,
    )


def verify_extremal_graph(path: Path = DEFAULT_GRAPH_PATH) -> ExtremalGraphFacts:
    return verify_extremal_graph_bytes(path.read_bytes(), source=str(path))


def derive_minimum_anchor_vacuity(graph: ExtremalGraphFacts) -> MinimumAnchorFacts:
    """Check the handshake/classification contradiction for minimum c=10."""

    _require(
        TRUSTED_R45_20_MAXIMUM_EDGE_CLASS_COUNT == 1,
        "the published extremal level must contain one isomorphism class",
    )
    handshake_lower_bound = (
        EXPECTED_ORDER * MINIMUM_ANCHOR_CODEGREE + 1
    ) // 2
    _require(
        handshake_lower_bound == TRUSTED_R45_20_MAXIMUM_EDGES,
        "the minimum-degree lower bound must meet the published extremal bound",
    )
    _require(
        graph.edge_count == TRUSTED_R45_20_MAXIMUM_EDGES,
        "the authenticated representative must be extremal",
    )
    is_regular = graph.degrees == (MINIMUM_ANCHOR_CODEGREE,) * EXPECTED_ORDER
    _require(
        not is_regular,
        "the unique extremal representative unexpectedly became 10-regular",
    )
    _require(
        min(graph.degrees) == 9,
        "the unique extremal representative must have minimum degree 9",
    )

    # If delta(G) = 10, handshaking gives e(G) >= 100.  The published upper
    # bound gives equality, hence every one of the twenty degrees is 10.  The
    # unique extremal class checked above is not regular, so no such G exists.
    return MinimumAnchorFacts(
        anchor_codegree=MINIMUM_ANCHOR_CODEGREE,
        handshake_edge_lower_bound=handshake_lower_bound,
        trusted_extremal_edge_upper_bound=TRUSTED_R45_20_MAXIMUM_EDGES,
        trusted_extremal_class_count=TRUSTED_R45_20_MAXIMUM_EDGE_CLASS_COUNT,
        unique_extremal_graph_is_regular=is_regular,
        d20_c10_minimum_anchor_empty=True,
    )


def _catalogue_record_count(path: Path) -> int:
    try:
        records = path.read_text(encoding="ascii").splitlines()
    except UnicodeDecodeError as error:
        raise VerificationError(f"{path}: catalogue is not ASCII") from error
    _require(all(record for record in records), f"{path}: blank graph6 record")
    return len(records)


def derive_branch_counts(directory: Path = HERE) -> BranchCountFacts:
    counts = {
        codegree: _catalogue_record_count(directory / f"r35_{codegree}.g6")
        for codegree in EXPECTED_R35_COUNTS
    }
    _require(
        counts == EXPECTED_R35_COUNTS,
        f"unexpected R(3,5) catalogue counts: {counts}",
    )

    # K43: d18,c=0..9 and d20,c=2..10.
    k43_before = sum(counts[c] for c in range(0, 10)) + sum(
        counts[c] for c in range(2, 11)
    )
    # K45: d20,c=2..10 and d22,c=4..10.
    k45_before = sum(counts[c] for c in range(2, 11)) + sum(
        counts[c] for c in range(4, 11)
    )
    eliminated = counts[10]
    k43_after = k43_before - eliminated
    k45_after = k45_before - eliminated

    _require(k43_before == EXPECTED_K43_TIGHT_BEFORE, "unexpected K43 total")
    _require(k43_after == EXPECTED_K43_TIGHT_AFTER, "unexpected reduced K43 total")
    _require(k45_before == EXPECTED_K45_TIGHT_BEFORE, "unexpected K45 total")
    _require(k45_after == EXPECTED_K45_TIGHT_AFTER, "unexpected reduced K45 total")

    return BranchCountFacts(
        r35_counts=tuple(sorted(counts.items())),
        eliminated_d20_c10_types=eliminated,
        k43_before=k43_before,
        k43_after=k43_after,
        k45_before=k45_before,
        k45_after=k45_after,
    )


def verify(
    graph_path: Path = DEFAULT_GRAPH_PATH, catalogue_directory: Path = HERE
) -> VerificationReport:
    graph = verify_extremal_graph(graph_path)
    minimum_anchor = derive_minimum_anchor_vacuity(graph)
    branch_counts = derive_branch_counts(catalogue_directory)
    return VerificationReport(
        official_graph=graph,
        minimum_anchor=minimum_anchor,
        branch_counts=branch_counts,
        classification_scope=(
            "Conditional on the current ANU catalogue facts E(4,5,20)=100 "
            "and exactly one isomorphism class at 100 edges; the local "
            "verifier authenticates and checks the "
            "unique representative but does not certify enumeration completeness."
        ),
    )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--graph", type=Path, default=DEFAULT_GRAPH_PATH)
    parser.add_argument("--catalogue-directory", type=Path, default=HERE)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        report = verify(args.graph, args.catalogue_directory)
    except (OSError, ValueError, VerificationError) as error:
        print(f"verification failed: {error}")
        return 1
    print(json.dumps(asdict(report), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
