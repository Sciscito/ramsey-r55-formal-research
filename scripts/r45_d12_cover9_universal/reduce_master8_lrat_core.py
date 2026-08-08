#!/usr/bin/env python3
"""Extract the initial-clause core used by a text LRAT refutation.

The reducer is deliberately conservative.  It supports the RUP-only Master8
certificate, follows every hint backwards from the final empty clause, keeps
the selected DIMACS clauses in their original order, densely remaps all clause
identifiers, and preserves filtered deletion actions at their original proof
positions.  Text LRAT RAT additions are parsed and counted, but reduction is
refused when one is present: changing the initial formula changes the active
occurrence set whose exhaustiveness a RAT step must establish.

The produced pair does not rely on this program for soundness.  It is intended
to be replayed by the same LRAT checker as the original pair.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from array import array
from dataclasses import dataclass
from pathlib import Path
from typing import BinaryIO, Iterable, Iterator, Sequence


HERE = Path(__file__).resolve().parent
REPOSITORY = HERE.parents[1]

MASTER_CNF_NAME = "cover6_closed_master_d8_bounded13.cnf"
MASTER_LRAT_NAME = "cover6_closed_master_d8_bounded13.lrat"
MASTER_VARIABLES = 66
MASTER_CLAUSES = 3_367_459
MASTER_CNF_BYTES = 189_298_375
MASTER_LRAT_BYTES = 128_131_809
MASTER_CNF_SHA256 = (
    "3E725132C29E1CAA9D5FD5EA0AD67D8A5A80E61A1241768D36A910DD23FD329D"
)
MASTER_LRAT_SHA256 = (
    "B2ECDACD2D99CD6EA2929C0B370C6AAFD74FE78FDE20FFBDFE68B7D0EF860505"
)


class CoreReductionError(ValueError):
    """The source pair or its dependency graph is not safely reducible."""


class RatReductionUnsupported(CoreReductionError):
    """The conservative reducer encountered a RAT addition."""


@dataclass(frozen=True)
class Addition:
    clause_id: int
    clause: tuple[int, ...]
    rup_hints: tuple[int, ...]
    rat_hints: tuple[tuple[int, tuple[int, ...]], ...]

    @property
    def dependencies(self) -> Iterator[int]:
        yield from self.rup_hints
        for target, hints in self.rat_hints:
            yield target
            yield from hints


@dataclass(frozen=True)
class Deletion:
    clause_ids: tuple[int, ...]


Action = Addition | Deletion | None


@dataclass(frozen=True)
class ProofIndex:
    initial_id: int
    final_id: int
    offsets: array
    lines: int
    additions: int
    deletions: int
    deletion_ids: int
    rup_additions: int
    rat_additions: int
    empty_additions: int


@dataclass(frozen=True)
class DependencyCore:
    initial_used: bytearray
    derived_used: bytearray
    dependency_edges: int

    @property
    def initial_count(self) -> int:
        return self.initial_used.count(1)

    @property
    def derived_count(self) -> int:
        return self.derived_used.count(1)


def sha256_file(path: Path) -> tuple[str, int]:
    digest = hashlib.sha256()
    size = 0
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            digest.update(block)
            size += len(block)
    return digest.hexdigest().upper(), size


def _positive(token: bytes, context: str) -> int:
    if not token.isdigit():
        raise CoreReductionError(f"{context}: expected a positive integer")
    value = int(token)
    if value == 0:
        raise CoreReductionError(f"{context}: zero is not a clause identifier")
    return value


def parse_lrat_line(raw: bytes, line_number: int) -> Action:
    stripped = raw.strip()
    if not stripped or stripped.startswith(b"c"):
        return None
    tokens = stripped.split()
    context = f"LRAT line {line_number}"
    if len(tokens) < 3:
        raise CoreReductionError(f"{context}: truncated action")
    clause_id = _positive(tokens[0], context)
    if tokens[1] == b"d":
        if tokens[-1] != b"0" or b"0" in tokens[2:-1]:
            raise CoreReductionError(f"{context}: malformed deletion")
        return Deletion(tuple(_positive(token, context) for token in tokens[2:-1]))

    try:
        clause_end = tokens.index(b"0", 1)
    except ValueError as error:
        raise CoreReductionError(f"{context}: missing clause terminator") from error
    if tokens[-1] != b"0" or clause_end == len(tokens) - 1:
        raise CoreReductionError(f"{context}: missing hint terminator")
    clause: list[int] = []
    for token in tokens[1:clause_end]:
        try:
            literal = int(token)
        except ValueError as error:
            raise CoreReductionError(f"{context}: malformed literal") from error
        if literal == 0:
            raise CoreReductionError(f"{context}: interior zero in clause")
        clause.append(literal)

    rup: list[int] = []
    rat: list[tuple[int, tuple[int, ...]]] = []
    current_target: int | None = None
    current_hints: list[int] = []
    for token in tokens[clause_end + 1:-1]:
        try:
            value = int(token)
        except ValueError as error:
            raise CoreReductionError(f"{context}: malformed hint") from error
        if value == 0:
            raise CoreReductionError(f"{context}: interior zero in hints")
        if value < 0:
            if current_target is not None:
                rat.append((current_target, tuple(current_hints)))
            current_target = -value
            current_hints = []
        elif current_target is None:
            rup.append(value)
        else:
            current_hints.append(value)
    if current_target is not None:
        rat.append((current_target, tuple(current_hints)))
    if not clause and rat:
        raise CoreReductionError(f"{context}: empty addition cannot have RAT hints")
    return Addition(clause_id, tuple(clause), tuple(rup), tuple(rat))


def read_cnf_header(path: Path) -> tuple[int, int]:
    with path.open("rb") as stream:
        for raw in stream:
            stripped = raw.strip()
            if not stripped or stripped.startswith(b"c"):
                continue
            fields = stripped.split()
            if len(fields) != 4 or fields[:2] != [b"p", b"cnf"]:
                raise CoreReductionError("expected a DIMACS 'p cnf' header")
            variables = _positive(fields[2], "DIMACS header")
            clauses = _positive(fields[3], "DIMACS header")
            return variables, clauses
    raise CoreReductionError("DIMACS header is missing")


def index_proof(path: Path, initial_clauses: int) -> ProofIndex:
    offsets = array("Q")
    first_id: int | None = None
    expected_id: int | None = None
    final_id: int | None = None
    lines = deletions = deletion_ids = rup = rat = empties = 0
    last_semantic_action: Action = None
    with path.open("rb", buffering=8 * 1024 * 1024) as stream:
        while True:
            offset = stream.tell()
            raw = stream.readline()
            if not raw:
                break
            lines += 1
            action = parse_lrat_line(raw, lines)
            if action is None:
                continue
            last_semantic_action = action
            if isinstance(action, Deletion):
                deletions += 1
                deletion_ids += len(action.clause_ids)
                continue
            if first_id is None:
                first_id = action.clause_id
                expected_id = first_id
            if action.clause_id != expected_id:
                raise CoreReductionError(
                    f"non-contiguous addition id {action.clause_id}; expected {expected_id}"
                )
            if action.clause_id != initial_clauses + 1 + len(offsets):
                raise CoreReductionError("proof additions do not start immediately after the CNF")
            for dependency in action.dependencies:
                if dependency >= action.clause_id:
                    raise CoreReductionError(
                        f"clause {action.clause_id} has non-backward hint {dependency}"
                    )
            offsets.append(offset)
            final_id = action.clause_id
            expected_id += 1
            if action.rat_hints:
                rat += 1
            else:
                rup += 1
            if not action.clause:
                empties += 1
    if first_id is None or final_id is None:
        raise CoreReductionError("LRAT proof has no additions")
    if not isinstance(last_semantic_action, Addition) or last_semantic_action.clause:
        raise CoreReductionError("last LRAT action is not an empty-clause addition")
    if empties != 1:
        raise CoreReductionError(f"expected exactly one empty addition, found {empties}")
    return ProofIndex(
        initial_id=first_id,
        final_id=final_id,
        offsets=offsets,
        lines=lines,
        additions=len(offsets),
        deletions=deletions,
        deletion_ids=deletion_ids,
        rup_additions=rup,
        rat_additions=rat,
        empty_additions=empties,
    )


def dependency_core(
    proof_path: Path, index: ProofIndex, initial_clauses: int
) -> DependencyCore:
    initial_used = bytearray(initial_clauses + 1)
    derived_used = bytearray(index.additions)
    derived_used[-1] = 1
    edges = 0
    with proof_path.open("rb", buffering=8 * 1024 * 1024) as stream:
        for position in range(index.additions - 1, -1, -1):
            if not derived_used[position]:
                continue
            stream.seek(index.offsets[position])
            action = parse_lrat_line(stream.readline(), -1)
            if not isinstance(action, Addition):
                raise CoreReductionError("indexed LRAT offset is not an addition")
            expected_id = index.initial_id + position
            if action.clause_id != expected_id:
                raise CoreReductionError("LRAT changed between indexing and dependency scan")
            for dependency in action.dependencies:
                edges += 1
                if dependency <= initial_clauses:
                    initial_used[dependency] = 1
                elif dependency < index.initial_id:
                    raise CoreReductionError(f"hint {dependency} falls in an unmapped id gap")
                else:
                    dependency_position = dependency - index.initial_id
                    if not 0 <= dependency_position < position:
                        raise CoreReductionError(
                            f"clause {action.clause_id} has invalid dependency {dependency}"
                        )
                    derived_used[dependency_position] = 1
    return DependencyCore(initial_used, derived_used, edges)


def kept_deletions(
    proof_path: Path,
    index: ProofIndex,
    core: DependencyCore,
    initial_clauses: int,
) -> tuple[int, int]:
    actions = identifiers = 0
    with proof_path.open("rb", buffering=8 * 1024 * 1024) as stream:
        for line_number, raw in enumerate(stream, 1):
            action = parse_lrat_line(raw, line_number)
            if not isinstance(action, Deletion):
                continue
            kept = 0
            for clause_id in action.clause_ids:
                if clause_id <= initial_clauses:
                    kept += int(bool(core.initial_used[clause_id]))
                elif index.initial_id <= clause_id <= index.final_id:
                    kept += int(bool(core.derived_used[clause_id - index.initial_id]))
            if kept:
                actions += 1
                identifiers += kept
    return actions, identifiers


def verify_master_identity(cnf: Path, lrat: Path) -> dict[str, object]:
    cnf_hash, cnf_bytes = sha256_file(cnf)
    lrat_hash, lrat_bytes = sha256_file(lrat)
    if (cnf_hash, cnf_bytes) != (MASTER_CNF_SHA256, MASTER_CNF_BYTES):
        raise CoreReductionError("Master8 CNF identity mismatch")
    if (lrat_hash, lrat_bytes) != (MASTER_LRAT_SHA256, MASTER_LRAT_BYTES):
        raise CoreReductionError("Master8 LRAT identity mismatch")
    variables, clauses = read_cnf_header(cnf)
    if (variables, clauses) != (MASTER_VARIABLES, MASTER_CLAUSES):
        raise CoreReductionError("Master8 DIMACS header mismatch")
    return {
        "cnf": {"bytes": cnf_bytes, "sha256": cnf_hash},
        "lrat": {"bytes": lrat_bytes, "sha256": lrat_hash},
        "variables": variables,
        "initial_clauses": clauses,
    }


def analyze(cnf: Path, lrat: Path, *, master_identity: bool = True) -> dict[str, object]:
    if master_identity:
        identity = verify_master_identity(cnf, lrat)
        variables = int(identity["variables"])
        initial_clauses = int(identity["initial_clauses"])
    else:
        variables, initial_clauses = read_cnf_header(cnf)
        cnf_hash, cnf_bytes = sha256_file(cnf)
        lrat_hash, lrat_bytes = sha256_file(lrat)
        identity = {
            "cnf": {"bytes": cnf_bytes, "sha256": cnf_hash},
            "lrat": {"bytes": lrat_bytes, "sha256": lrat_hash},
            "variables": variables,
            "initial_clauses": initial_clauses,
        }
    index = index_proof(lrat, initial_clauses)
    core = dependency_core(lrat, index, initial_clauses)
    deletion_actions, deletion_ids = kept_deletions(
        lrat, index, core, initial_clauses
    )
    status = "PASS_RUP_CORE_ANALYSIS" if index.rat_additions == 0 else "RAT_REDUCTION_REFUSED"
    return {
        "schema_version": 1,
        "status": status,
        "input": identity,
        "proof": {
            "lines": index.lines,
            "additions": index.additions,
            "rup_additions": index.rup_additions,
            "rat_additions": index.rat_additions,
            "deletion_actions": index.deletions,
            "deleted_identifiers": index.deletion_ids,
            "first_addition_id": index.initial_id,
            "final_empty_id": index.final_id,
        },
        "core": {
            "initial_clauses": core.initial_count,
            "derived_additions": core.derived_count,
            "dependency_edges": core.dependency_edges,
            "retained_deletion_actions": deletion_actions,
            "retained_deleted_identifiers": deletion_ids,
        },
        "rat_policy": (
            "safe RUP-only remap; RAT input is detected and reduction is refused"
        ),
        "scope": (
            "syntactic LRAT dependency extraction only; the reduced pair must be "
            "replayed by a trusted LRAT checker"
        ),
        "_index": index,
        "_core": core,
    }


def _canonical_clause(raw: bytes, variables: int, clause_number: int) -> bytes:
    fields = raw.split()
    if not fields or fields[-1] != b"0" or b"0" in fields[:-1]:
        raise CoreReductionError(f"malformed DIMACS clause {clause_number}")
    for token in fields[:-1]:
        try:
            literal = int(token)
        except ValueError as error:
            raise CoreReductionError(
                f"non-integer literal in DIMACS clause {clause_number}"
            ) from error
        if literal == 0 or abs(literal) > variables:
            raise CoreReductionError(f"out-of-range literal in clause {clause_number}")
    return b" ".join(fields) + b"\n"


def _dimacs_clauses(path: Path) -> Iterator[tuple[int, bytes]]:
    variables, expected_clauses = read_cnf_header(path)
    header_seen = False
    clause_number = 0
    with path.open("rb", buffering=8 * 1024 * 1024) as stream:
        for raw in stream:
            stripped = raw.strip()
            if not stripped or stripped.startswith(b"c"):
                continue
            if not header_seen:
                header_seen = True
                continue
            clause_number += 1
            yield clause_number, _canonical_clause(raw, variables, clause_number)
    if clause_number != expected_clauses:
        raise CoreReductionError(
            f"DIMACS clause count changed: {clause_number} != {expected_clauses}"
        )


def _mapping_header(source_clause_label: str) -> bytes:
    try:
        encoded = source_clause_label.encode("ascii")
    except UnicodeEncodeError as error:
        raise CoreReductionError("mapping source label must be ASCII") from error
    if not encoded or any(character in encoded for character in b"\t\r\n"):
        raise CoreReductionError("mapping source label is empty or contains whitespace")
    return b"core_clause_id\t" + encoded + b"\tclause_sha256"


def verify_clause_mapping(
    master_cnf: Path,
    core_cnf: Path,
    mapping_path: Path,
    *,
    source_clause_label: str = "master8_clause_id",
) -> dict[str, object]:
    master_variables, master_count = read_cnf_header(master_cnf)
    core_variables, core_count = read_cnf_header(core_cnf)
    if core_variables != master_variables:
        raise CoreReductionError(
            "core CNF variable count differs from the source CNF: "
            f"{core_variables} != {master_variables}"
        )
    mapping_hash, mapping_bytes = sha256_file(mapping_path)
    rows: list[tuple[int, int, str]] = []
    with mapping_path.open("rb") as stream:
        header = stream.readline().rstrip(b"\r\n")
        if header != _mapping_header(source_clause_label):
            raise CoreReductionError("unexpected clause-mapping header")
        previous_master = 0
        for line_number, raw in enumerate(stream, 2):
            fields = raw.rstrip(b"\r\n").split(b"\t")
            if len(fields) != 3:
                raise CoreReductionError(f"malformed mapping row {line_number}")
            core_id = _positive(fields[0], f"mapping row {line_number}")
            master_id = _positive(fields[1], f"mapping row {line_number}")
            try:
                clause_hash = fields[2].decode("ascii").upper()
            except UnicodeDecodeError as error:
                raise CoreReductionError(f"non-ASCII mapping hash at row {line_number}") from error
            if len(clause_hash) != 64 or any(
                character not in "0123456789ABCDEF" for character in clause_hash
            ):
                raise CoreReductionError(f"malformed mapping hash at row {line_number}")
            if core_id != len(rows) + 1 or not previous_master < master_id <= master_count:
                raise CoreReductionError("mapping ids are not ordered one-to-one")
            rows.append((core_id, master_id, clause_hash))
            previous_master = master_id
    if len(rows) != core_count:
        raise CoreReductionError(f"mapping rows differ from core clauses: {len(rows)}")

    row_position = 0
    core_iterator = iter(_dimacs_clauses(core_cnf))
    for master_id, master_clause in _dimacs_clauses(master_cnf):
        if row_position == len(rows):
            continue
        core_id, selected_master_id, expected_hash = rows[row_position]
        if master_id != selected_master_id:
            continue
        observed_core_id, core_clause = next(core_iterator)
        if observed_core_id != core_id or core_clause != master_clause:
            raise CoreReductionError(f"mapped clause content differs at core id {core_id}")
        if hashlib.sha256(core_clause).hexdigest().upper() != expected_hash:
            raise CoreReductionError(f"mapped clause hash differs at core id {core_id}")
        row_position += 1
    if row_position != len(rows):
        raise CoreReductionError("not every mapping row was found in the Master8 CNF")
    try:
        next(core_iterator)
    except StopIteration:
        pass
    else:
        raise CoreReductionError("core CNF contains clauses absent from the mapping")
    return {
        "status": "PASS_EXACT_ORDERED_SUBSEQUENCE",
        "rows": len(rows),
        "master_clauses": master_count,
        "core_clauses": core_count,
        "master_variables": master_variables,
        "core_variables": core_variables,
        "mapping": {"bytes": mapping_bytes, "sha256": mapping_hash},
    }


class HashingWriter:
    def __init__(self, stream: BinaryIO):
        self.stream = stream
        self.digest = hashlib.sha256()
        self.bytes = 0
        self.lines = 0

    def write(self, payload: bytes) -> None:
        self.stream.write(payload)
        self.digest.update(payload)
        self.bytes += len(payload)
        self.lines += payload.count(b"\n")

    def metadata(self) -> dict[str, object]:
        return {
            "bytes": self.bytes,
            "lines": self.lines,
            "sha256": self.digest.hexdigest().upper(),
        }


def write_core_cnf(
    source: Path,
    target: Path,
    mapping_target: Path,
    variables: int,
    initial_clauses: int,
    core: DependencyCore,
    *,
    source_clause_label: str = "master8_clause_id",
) -> tuple[array, dict[str, object], dict[str, object]]:
    mapping = array("I", [0]) * (initial_clauses + 1)
    clause_number = kept = 0
    with (
        source.open("rb", buffering=8 * 1024 * 1024) as inp,
        target.open("xb") as raw_out,
        mapping_target.open("xb") as raw_mapping,
    ):
        out = HashingWriter(raw_out)
        mapping_out = HashingWriter(raw_mapping)
        out.write(f"p cnf {variables} {core.initial_count}\n".encode("ascii"))
        mapping_out.write(_mapping_header(source_clause_label) + b"\n")
        header_seen = False
        for raw in inp:
            stripped = raw.strip()
            if not stripped or stripped.startswith(b"c"):
                continue
            if not header_seen:
                fields = stripped.split()
                if fields != [b"p", b"cnf", str(variables).encode(), str(initial_clauses).encode()]:
                    raise CoreReductionError("DIMACS header changed during reduction")
                header_seen = True
                continue
            clause_number += 1
            canonical = _canonical_clause(raw, variables, clause_number)
            if core.initial_used[clause_number]:
                kept += 1
                mapping[clause_number] = kept
                out.write(canonical)
                clause_hash = hashlib.sha256(canonical).hexdigest().upper()
                mapping_out.write(
                    f"{kept}\t{clause_number}\t{clause_hash}\n".encode("ascii")
                )
        if not header_seen or clause_number != initial_clauses:
            raise CoreReductionError(
                f"DIMACS clause count changed: {clause_number} != {initial_clauses}"
            )
        if kept != core.initial_count:
            raise CoreReductionError("not every selected initial clause was emitted")
        metadata = out.metadata()
        mapping_metadata = mapping_out.metadata()
    return (
        mapping,
        {"variables": variables, "clauses": kept, **metadata},
        {"rows": kept, **mapping_metadata},
    )


def _map_id(
    old_id: int,
    initial_clauses: int,
    index: ProofIndex,
    initial_map: array,
    derived_map: array,
) -> int:
    if old_id <= initial_clauses:
        mapped = initial_map[old_id]
    elif index.initial_id <= old_id <= index.final_id:
        mapped = derived_map[old_id - index.initial_id]
    else:
        raise CoreReductionError(f"cannot map clause id {old_id}")
    if mapped == 0:
        raise CoreReductionError(f"clause id {old_id} is used before it is mapped")
    return mapped


def _addition_line(
    action: Addition,
    new_id: int,
    mapped_rup: Sequence[int],
) -> bytes:
    fields: list[str] = [str(new_id)]
    fields.extend(map(str, action.clause))
    fields.append("0")
    fields.extend(map(str, mapped_rup))
    fields.append("0")
    return (" ".join(fields) + "\n").encode("ascii")


def write_core_lrat(
    source: Path,
    target: Path,
    initial_clauses: int,
    index: ProofIndex,
    core: DependencyCore,
    initial_map: array,
) -> dict[str, object]:
    if index.rat_additions:
        raise RatReductionUnsupported(
            "RAT additions require an occurrence-exhaustiveness proof after CNF trimming"
        )
    derived_map = array("I", [0]) * index.additions
    additions = deletion_actions = deletion_ids = kept_additions = 0
    with source.open("rb", buffering=8 * 1024 * 1024) as inp, target.open("xb") as raw_out:
        out = HashingWriter(raw_out)
        for line_number, raw in enumerate(inp, 1):
            action = parse_lrat_line(raw, line_number)
            if action is None:
                continue
            if isinstance(action, Addition):
                position = action.clause_id - index.initial_id
                if not 0 <= position < index.additions:
                    raise CoreReductionError("addition id changed during output pass")
                additions += 1
                if not core.derived_used[position]:
                    continue
                kept_additions += 1
                new_id = core.initial_count + kept_additions
                mapped_hints = tuple(
                    _map_id(
                        hint,
                        initial_clauses,
                        index,
                        initial_map,
                        derived_map,
                    )
                    for hint in action.rup_hints
                )
                derived_map[position] = new_id
                out.write(_addition_line(action, new_id, mapped_hints))
            else:
                mapped: list[int] = []
                for old_id in action.clause_ids:
                    selected = (
                        bool(core.initial_used[old_id])
                        if old_id <= initial_clauses
                        else (
                            index.initial_id <= old_id <= index.final_id
                            and bool(core.derived_used[old_id - index.initial_id])
                        )
                    )
                    if selected:
                        mapped.append(
                            _map_id(
                                old_id,
                                initial_clauses,
                                index,
                                initial_map,
                                derived_map,
                            )
                        )
                if mapped:
                    deletion_actions += 1
                    deletion_ids += len(mapped)
                    out.write(
                        ("1 d " + " ".join(map(str, mapped)) + " 0\n").encode("ascii")
                    )
        if additions != index.additions or kept_additions != core.derived_count:
            raise CoreReductionError("not every selected proof addition was emitted")
        metadata = out.metadata()
    return {
        "additions": kept_additions,
        "deletion_actions": deletion_actions,
        "deleted_identifiers": deletion_ids,
        **metadata,
    }


def _public_analysis(analysis: dict[str, object]) -> dict[str, object]:
    return {key: value for key, value in analysis.items() if not key.startswith("_")}


def verify_reduced_pair(cnf: Path, lrat: Path) -> dict[str, object]:
    analysis = analyze(cnf, lrat, master_identity=False)
    index = analysis["_index"]
    core = analysis["_core"]
    assert isinstance(index, ProofIndex)
    assert isinstance(core, DependencyCore)
    initial_clauses = int(analysis["input"]["initial_clauses"])
    if index.rat_additions:
        raise RatReductionUnsupported("reduced proof unexpectedly contains RAT additions")
    if core.initial_count != initial_clauses:
        raise CoreReductionError("reduced CNF still contains an unused initial clause")
    if core.derived_count != index.additions:
        raise CoreReductionError("reduced LRAT still contains an unused addition")
    return {
        **_public_analysis(analysis),
        "status": "PASS_CLOSED_RUP_DEPENDENCY_CORE_REPLAY_STILL_REQUIRED",
    }


def reduce_pair(
    cnf: Path,
    lrat: Path,
    output_dir: Path,
    *,
    master_identity: bool = True,
    require_repository_output: bool = True,
) -> dict[str, object]:
    analysis = analyze(cnf, lrat, master_identity=master_identity)
    index = analysis["_index"]
    core = analysis["_core"]
    assert isinstance(index, ProofIndex)
    assert isinstance(core, DependencyCore)
    if index.rat_additions:
        raise RatReductionUnsupported("Master8 proof unexpectedly contains RAT additions")

    if require_repository_output:
        resolved_output = output_dir.resolve()
        resolved_repository = REPOSITORY.resolve()
        if (
            resolved_output == resolved_repository
            or resolved_repository not in resolved_output.parents
        ):
            raise CoreReductionError(
                "output directory must be a new directory inside the repository"
            )
    output_dir.mkdir(parents=True, exist_ok=False)
    cnf_target = output_dir / "cover6_closed_master_d8_bounded13_core.cnf"
    lrat_target = output_dir / "cover6_closed_master_d8_bounded13_core.lrat"
    mapping_target = output_dir / "core_clause_map.tsv"
    report_target = output_dir / "reduction.json"
    cnf_partial = output_dir / f"{cnf_target.name}.partial"
    lrat_partial = output_dir / f"{lrat_target.name}.partial"
    mapping_partial = output_dir / f"{mapping_target.name}.partial"
    report_partial = output_dir / f"{report_target.name}.partial"
    variables = int(analysis["input"]["variables"])
    initial_clauses = int(analysis["input"]["initial_clauses"])
    partials = (cnf_partial, lrat_partial, mapping_partial, report_partial)
    try:
        initial_map, cnf_metadata, mapping_metadata = write_core_cnf(
            cnf,
            cnf_partial,
            mapping_partial,
            variables,
            initial_clauses,
            core,
        )
        lrat_metadata = write_core_lrat(
            lrat, lrat_partial, initial_clauses, index, core, initial_map
        )
        expected_cnf = analysis["input"]["cnf"]
        expected_lrat = analysis["input"]["lrat"]
        observed_cnf_hash, observed_cnf_bytes = sha256_file(cnf)
        observed_lrat_hash, observed_lrat_bytes = sha256_file(lrat)
        if (observed_cnf_hash, observed_cnf_bytes) != (
            expected_cnf["sha256"],
            expected_cnf["bytes"],
        ):
            raise CoreReductionError("source CNF changed during reduction")
        if (observed_lrat_hash, observed_lrat_bytes) != (
            expected_lrat["sha256"],
            expected_lrat["bytes"],
        ):
            raise CoreReductionError("source LRAT changed during reduction")
        report = {
            **_public_analysis(analysis),
            "status": "REDUCED_PAIR_WRITTEN_REPLAY_REQUIRED",
            "output": {
                "cnf": {"name": cnf_target.name, **cnf_metadata},
                "lrat": {"name": lrat_target.name, **lrat_metadata},
                "initial_clause_mapping": {
                    "name": mapping_target.name,
                    **mapping_metadata,
                },
            },
        }
        with report_partial.open("xb") as stream:
            stream.write(
                (json.dumps(report, indent=2, sort_keys=True) + "\n").encode("utf-8")
            )
        os.replace(cnf_partial, cnf_target)
        os.replace(lrat_partial, lrat_target)
        os.replace(mapping_partial, mapping_target)
        os.replace(report_partial, report_target)
    except BaseException:
        for partial in partials:
            if partial.exists():
                partial.unlink()
        if output_dir.exists() and not any(output_dir.iterdir()):
            output_dir.rmdir()
        raise
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "command",
        choices=("analyze", "reduce", "verify-core"),
        nargs="?",
        default="analyze",
    )
    parser.add_argument("--cnf", type=Path, required=True)
    parser.add_argument("--lrat", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    if args.command == "analyze":
        result = _public_analysis(analyze(args.cnf, args.lrat, master_identity=True))
    elif args.command == "verify-core":
        result = verify_reduced_pair(args.cnf, args.lrat)
    else:
        if args.output_dir is None:
            parser.error("reduce requires --output-dir")
        result = reduce_pair(args.cnf, args.lrat, args.output_dir)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
