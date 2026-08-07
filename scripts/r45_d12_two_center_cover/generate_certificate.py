#!/usr/bin/env python3
"""Generate or verify the 64-pattern two-centre ``gen4412`` certificate.

The heavy JSON certificate is deliberately external to the repository.  The
``generate`` command only writes to an explicit absolute ``S:`` path.  The
``verify`` command always regenerates all 26,845 assignments and, when given a
certificate path, compares its bytes with the deterministic regeneration.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PureWindowsPath
from typing import Sequence


ORDER = 12
EDGE_COUNT = ORDER * (ORDER - 1) // 2
ALL_EDGES = (1 << EDGE_COUNT) - 1
AMBIENT_ORDER = 24
BLUE_BLOCK_OFFSET = 12
EXPECTED_SOURCE_SHA256 = "317F7D55DEAB37EC2AA98557F7F483F55281AFF04BFC8E4ECDA1CF2DEEDF0385"
EXPECTED_PARENTS = 26_845
EXPECTED_CHILD_INSTANCES = 1_449_166
EXPECTED_PROJECTED = 21_468
EXPECTED_ISOMORPHISM_CLASSES = 857
EXPECTED_PATTERNS = 64

Pattern = tuple[int, int]  # fixed mask, red mask; fixed non-red means blue
Profile = tuple[int, int]
TwoCenterKey = tuple[int, tuple[Profile, ...]]

PAIRS = [(i, j) for i in range(ORDER) for j in range(i + 1, ORDER)]
PAIR_INDEX = {pair: index for index, pair in enumerate(PAIRS)}


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest().upper()


def require_ssd_path(path: Path) -> None:
    windows = PureWindowsPath(str(path))
    if windows.drive.upper() != "S:" or not windows.is_absolute():
        raise ValueError("certificate output must be an explicit absolute S: path")


def decode_edges(encoded: int, order: int = ORDER) -> tuple[int, ...]:
    edge_count = order * (order - 1) // 2
    value = encoded
    reversed_digits = []
    for _ in range(edge_count):
        value, digit = divmod(value, 3)
        reversed_digits.append(digit)
    if value != 1:
        raise ValueError(f"invalid order-{order} base-3 sentinel: {value}")
    return tuple(reversed(reversed_digits))


def pattern_from_edges(edges: Sequence[int]) -> Pattern:
    if len(edges) != EDGE_COUNT:
        raise ValueError(f"expected {EDGE_COUNT} edge digits")
    fixed = 0
    red = 0
    for edge_index, colour in enumerate(edges):
        if colour not in (0, 1, 2):
            raise ValueError(f"invalid ternary colour {colour}")
        if colour:
            fixed |= 1 << edge_index
        if colour == 2:
            red |= 1 << edge_index
    return fixed, red


def dimacs_edge_variable(order: int, left: int, right: int) -> int:
    """Return the one-based upper-triangle DIMACS variable for ``(left,right)``."""
    if not 0 <= left < right < order:
        raise ValueError(f"invalid edge ({left},{right}) in K_{order}")
    return left * (2 * order - left - 1) // 2 + (right - left)


def raw_hol_dimacs_units(pattern: Pattern) -> tuple[int, ...]:
    """Emit raw-B SAT units: HOL blue 1 -> negative, HOL red 2 -> positive.

    The local B vertices occupy reduced vertices 12..23. Thus these literals
    use exactly DIMACS variables 211..276. This is Lean's ``.rawHOL``
    orientation, not the palette-swapped conditioned-cover orientation.
    """
    units = []
    for edge_index, (left, right) in enumerate(PAIRS):
        colour = ternary_digit(pattern, edge_index)
        if colour == 0:
            continue
        variable = dimacs_edge_variable(
            AMBIENT_ORDER, BLUE_BLOCK_OFFSET + left, BLUE_BLOCK_OFFSET + right
        )
        units.append(-variable if colour == 1 else variable)
    return tuple(units)


def load_parents(path: Path) -> tuple[list[Pattern], list[int]]:
    parents = []
    child_counts = []
    with path.open("rb") as stream:
        for line_number, raw_line in enumerate(stream, 1):
            fields = raw_line.strip().split()
            if len(fields) < 2:
                raise ValueError(f"{path}:{line_number}: malformed cover record")
            try:
                parent_id = int(fields[0], 10)
            except ValueError as exc:
                raise ValueError(f"{path}:{line_number}: invalid parent integer") from exc
            parents.append(pattern_from_edges(decode_edges(parent_id)))
            child_counts.append(len(fields) - 1)
    return parents, child_counts


def ternary_digit(pattern: Pattern, edge_index: int) -> int:
    fixed, red = pattern
    if not ((fixed >> edge_index) & 1):
        return 0
    return 2 if ((red >> edge_index) & 1) else 1


def projected_two_center(pattern: Pattern) -> Pattern:
    return pattern[0] & ((1 << 21) - 1), pattern[1] & ((1 << 21) - 1)


def two_center_key(pattern: Pattern, *, swap: bool = False) -> TwoCenterKey:
    central = ternary_digit(pattern, 0)
    profiles = []
    for vertex in range(2, ORDER):
        profile = (
            ternary_digit(pattern, vertex - 1),
            ternary_digit(pattern, vertex + 9),
        )
        profiles.append(tuple(reversed(profile)) if swap else profile)
    return central, tuple(sorted(profiles))


def canonical_two_center_key(pattern: Pattern) -> TwoCenterKey:
    return min(two_center_key(pattern), two_center_key(pattern, swap=True))


def profile_subsumes(weak: Profile, strong: Profile) -> bool:
    return all(left == 0 or left == right for left, right in zip(weak, strong))


def profile_matching(
    weak: Sequence[Profile], strong: Sequence[Profile]
) -> list[int] | None:
    """Map every weak profile position to a compatible strong position."""
    strong_for_weak = [-1] * len(weak)
    weak_for_strong = [-1] * len(strong)

    def augment(weak_index: int, seen: list[bool]) -> bool:
        for strong_index, strong_profile in enumerate(strong):
            if seen[strong_index] or not profile_subsumes(
                weak[weak_index], strong_profile
            ):
                continue
            seen[strong_index] = True
            previous = weak_for_strong[strong_index]
            if previous == -1 or augment(previous, seen):
                weak_for_strong[strong_index] = weak_index
                strong_for_weak[weak_index] = strong_index
                return True
        return False

    if all(augment(index, [False] * len(strong)) for index in range(len(weak))):
        return strong_for_weak
    return None


def two_center_subsumes(weak: TwoCenterKey, strong: TwoCenterKey) -> bool:
    weak_central, weak_profiles = weak
    strong_central, strong_profiles = strong
    if weak_central not in (0, strong_central):
        return False
    if profile_matching(weak_profiles, strong_profiles) is not None:
        return True
    swapped = tuple(sorted((right, left) for left, right in weak_profiles))
    return profile_matching(swapped, strong_profiles) is not None


def key_fixed_count(key: TwoCenterKey) -> int:
    central, profiles = key
    return int(central != 0) + sum(
        int(left != 0) + int(right != 0) for left, right in profiles
    )


def minimal_two_center_antichain(keys: set[TwoCenterKey]) -> list[TwoCenterKey]:
    ordered = sorted(keys, key=lambda key: (key_fixed_count(key), key))
    kept = []
    for candidate in ordered:
        if any(two_center_subsumes(weak, candidate) for weak in kept):
            continue
        kept.append(candidate)
    return kept


def permute_pattern(pattern: Pattern, new_to_old: Sequence[int]) -> Pattern:
    """Relabel using transformed[a,b] = source[new_to_old[a],new_to_old[b]]."""
    if sorted(new_to_old) != list(range(ORDER)):
        raise ValueError("new_to_old must be a permutation of 0..11")
    new_fixed = 0
    new_red = 0
    for new_edge, (new_left, new_right) in enumerate(PAIRS):
        old_left, old_right = sorted((new_to_old[new_left], new_to_old[new_right]))
        old_edge = PAIR_INDEX[(old_left, old_right)]
        colour = ternary_digit(pattern, old_edge)
        if colour:
            new_fixed |= 1 << new_edge
        if colour == 2:
            new_red |= 1 << new_edge
    return new_fixed, new_red


def directly_extends_weak(oriented: Pattern, weak: TwoCenterKey) -> bool:
    weak_central, weak_profiles = weak
    if weak_central not in (0, ternary_digit(oriented, 0)):
        return False
    for outside, weak_profile in zip(range(2, ORDER), weak_profiles, strict=True):
        strong_profile = (
            ternary_digit(oriented, outside - 1),
            ternary_digit(oriented, outside + 9),
        )
        if not profile_subsumes(weak_profile, strong_profile):
            return False
    return True


def orientation_to_weak(
    parent: Pattern, weak: TwoCenterKey
) -> tuple[Pattern, tuple[int, ...]] | None:
    weak_central, weak_profiles = weak
    if weak_central not in (0, ternary_digit(parent, 0)):
        return None
    for swap_centres in (False, True):
        centres = (1, 0) if swap_centres else (0, 1)
        outside = list(range(2, ORDER))
        strong_profiles = tuple(
            (
                ternary_digit(
                    parent, PAIR_INDEX[tuple(sorted((centres[0], vertex)))]
                ),
                ternary_digit(
                    parent, PAIR_INDEX[tuple(sorted((centres[1], vertex)))]
                ),
            )
            for vertex in outside
        )
        matching = profile_matching(weak_profiles, strong_profiles)
        if matching is None:
            continue
        new_to_old = (centres[0], centres[1]) + tuple(
            outside[strong_index] for strong_index in matching
        )
        oriented = permute_pattern(parent, new_to_old)
        if not directly_extends_weak(oriented, weak):
            raise AssertionError("constructed orientation does not extend weak key")
        return oriented, new_to_old
    return None


def consensus(patterns: Sequence[Pattern]) -> Pattern:
    if not patterns:
        raise ValueError("cannot form an empty consensus")
    fixed_in_all = ALL_EDGES
    red_in_all = ALL_EDGES
    red_in_any = 0
    for fixed, red in patterns:
        fixed_in_all &= fixed
        red_in_all &= red
        red_in_any |= red
    agreed_red = fixed_in_all & red_in_all
    agreed_blue = fixed_in_all & ~red_in_any & ALL_EDGES
    return agreed_red | agreed_blue, agreed_red


def extends_pattern(strong: Pattern, weak: Pattern) -> bool:
    strong_fixed, strong_red = strong
    weak_fixed, weak_red = weak
    return weak_fixed & ~strong_fixed == 0 and (weak_red ^ strong_red) & weak_fixed == 0


def serialize_key(key: TwoCenterKey) -> dict[str, object]:
    central, profiles = key
    return {
        "central": central,
        "outside_profiles": [list(profile) for profile in profiles],
        "fixed_units": key_fixed_count(key),
    }


def build_certificate(cover_path: Path) -> dict[str, object]:
    source_sha = sha256_file(cover_path)
    if source_sha != EXPECTED_SOURCE_SHA256:
        raise RuntimeError("unexpected gen4412 SHA-256")
    parents, child_counts = load_parents(cover_path)
    projections = {projected_two_center(parent) for parent in parents}
    classes = {canonical_two_center_key(pattern) for pattern in projections}
    weak_cover = minimal_two_center_antichain(classes)
    dimensions = (
        len(parents),
        sum(child_counts),
        len(projections),
        len(classes),
        len(weak_cover),
    )
    expected = (
        EXPECTED_PARENTS,
        EXPECTED_CHILD_INSTANCES,
        EXPECTED_PROJECTED,
        EXPECTED_ISOMORPHISM_CLASSES,
        EXPECTED_PATTERNS,
    )
    if dimensions != expected:
        raise RuntimeError(f"cover dimensions changed: {dimensions} != {expected}")

    groups: list[list[Pattern]] = [[] for _ in weak_cover]
    assignments = []
    for parent_index, parent in enumerate(parents, 1):
        for weak_index, weak in enumerate(weak_cover):
            result = orientation_to_weak(parent, weak)
            if result is None:
                continue
            oriented, permutation = result
            groups[weak_index].append(oriented)
            assignments.append(
                {
                    "parent_record_one_based": parent_index,
                    "pattern_one_based": weak_index + 1,
                    "new_to_old": list(permutation),
                }
            )
            break
        else:
            raise RuntimeError(f"parent record {parent_index} is uncovered")
    fused = [consensus(group) for group in groups]
    if len(assignments) != len(parents) or any(not group for group in groups):
        raise AssertionError("assignments are not a nonempty partition")
    if len(set(fused)) != EXPECTED_PATTERNS:
        raise AssertionError("fused patterns are not distinct")
    for weak, group, fused_pattern in zip(weak_cover, groups, fused, strict=True):
        if not all(directly_extends_weak(oriented, weak) for oriented in group):
            raise AssertionError("weak direct implication failed")
        if not all(extends_pattern(oriented, fused_pattern) for oriented in group):
            raise AssertionError("fused consensus implication failed")

    parent_records_by_pattern = [[] for _ in weak_cover]
    for assignment in assignments:
        parent_records_by_pattern[assignment["pattern_one_based"] - 1].append(
            assignment["parent_record_one_based"]
        )
    patterns = []
    for index, (weak, group, fused_pattern, parent_records) in enumerate(
        zip(weak_cover, groups, fused, parent_records_by_pattern, strict=True), 1
    ):
        fixed, red = fused_pattern
        patterns.append(
            {
                "index_one_based": index,
                "weak": serialize_key(weak),
                "fused_fixed_mask": fixed,
                "fused_red_mask": red,
                "fused_fixed_units": fixed.bit_count(),
                "fused_red_units": red.bit_count(),
                "assigned_parent_count": len(group),
                "assigned_parent_records_one_based": parent_records,
            }
        )

    return {
        "schema": "gen4412-two-centre-consensus-v1",
        "source": {
            "path": str(cover_path.resolve()),
            "sha256": source_sha,
            "parent_records": len(parents),
            "child_instances": sum(child_counts),
        },
        "colour_convention": {
            "0": "hole",
            "1": "blue / negative DIMACS unit",
            "2": "red / positive DIMACS unit",
        },
        "permutation_convention": (
            "new_to_old[a] is the original vertex used at canonical vertex a; "
            "the transformed colour of new edge (a,b) is the source colour of "
            "old edge (new_to_old[a],new_to_old[b])."
        ),
        "assignment_rule": (
            "weak patterns are sorted deterministically by fixed-unit count and "
            "key; each source parent is assigned to the first directly matching "
            "weak pattern, trying centre order (0,1) before (1,0) and the "
            "deterministic augmenting-path outside-profile matching."
        ),
        "checks": {
            "projected_oriented_patterns": len(projections),
            "projected_isomorphism_classes": len(classes),
            "weak_patterns": len(weak_cover),
            "fused_patterns": len(set(fused)),
            "assignments": len(assignments),
            "weak_direct_implications": len(assignments),
            "fused_consensus_implications": len(assignments),
        },
        "patterns": patterns,
        "assignments": assignments,
    }


def certificate_bytes(certificate: dict[str, object]) -> bytes:
    return (json.dumps(certificate, indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    generate = commands.add_parser("generate")
    generate.add_argument("cover", type=Path)
    generate.add_argument("output", type=Path)
    verify = commands.add_parser("verify")
    verify.add_argument("cover", type=Path)
    verify.add_argument("certificate", nargs="?", type=Path)
    args = parser.parse_args()

    regenerated = build_certificate(args.cover)
    data = certificate_bytes(regenerated)
    if args.command == "generate":
        require_ssd_path(args.output)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(data)
        status = "generated"
        path = args.output
    else:
        status = "regenerated"
        path = args.certificate
        if path is not None:
            if path.read_bytes() != data:
                raise RuntimeError("certificate differs from deterministic regeneration")
            status = "verified"
    result = {
        "status": status,
        "bytes": len(data),
        "sha256": hashlib.sha256(data).hexdigest().upper(),
        "assignments": len(regenerated["assignments"]),
        "patterns": len(regenerated["patterns"]),
        "pattern64": regenerated["patterns"][63],
    }
    if path is not None:
        result["path"] = str(path)
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
