#!/usr/bin/env python3
"""Render the FCUj_ selected-core semantics module from the audited F`GOW proof.

The mathematical proof is deliberately reused as a frozen template: only the
core API, exact family cardinalities, offsets, and compact witness payload are
specialised.  The renderer verifies both input identities, performs guarded
substitutions, and uses exclusive creation so a stale or partially edited
module cannot be overwritten silently.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Sequence


HERE = Path(__file__).resolve().parent
REPOSITORY = HERE.parents[1]
TEMPLATE_PATH = (
    REPOSITORY
    / "vendor"
    / "lrat-catcher"
    / "LRATCatcher"
    / "Tests"
    / "R44Cover6Master7R34FgraveGowSemantics.lean"
)
OUTPUT_PATH = TEMPLATE_PATH.with_name("R44Cover6Master7R34FCUjSemantics.lean")
PAYLOAD_PATH = HERE / "MASTER7_R34_FCUJ_CORE_SEMANTIC_WITNESSES_V1.bin"

TEMPLATE_SHA256 = (
    "9608990A7CD482A3526E7A7A788D8ED158F3FF3C34E9AA57087B331A4BB20493"
)
PAYLOAD_SHA256 = (
    "1509D60BF036DB9C8333357EA18B9C0E57C7FA14DF186F6C32EAE765F22DF97D"
)
PAYLOAD_CHARACTERS = 2_475


class FCUjSemanticsRenderError(ValueError):
    """Raised when the frozen template or payload contract changes."""


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest().upper()


def _replace_literal(text: str, old: str, new: str, expected: int) -> str:
    observed = text.count(old)
    if observed != expected:
        raise FCUjSemanticsRenderError(
            f"template occurrence count changed for {old!r}: {observed} != {expected}"
        )
    return text.replace(old, new)


def _replace_number(text: str, old: int, new: int, expected: int) -> str:
    pattern = re.compile(rf"\b{old}\b")
    observed = len(pattern.findall(text))
    if observed != expected:
        raise FCUjSemanticsRenderError(
            f"template numeric occurrence count changed for {old}: "
            f"{observed} != {expected}"
        )
    return pattern.sub(str(new), text)


def render_module(
    template_path: Path = TEMPLATE_PATH,
    payload_path: Path = PAYLOAD_PATH,
) -> bytes:
    template = template_path.read_bytes()
    if sha256_bytes(template) != TEMPLATE_SHA256:
        raise FCUjSemanticsRenderError("frozen F`GOW semantics template SHA-256 changed")
    payload = payload_path.read_bytes()
    if len(payload) != PAYLOAD_CHARACTERS:
        raise FCUjSemanticsRenderError("FCUj_ witness payload length changed")
    if sha256_bytes(payload) != PAYLOAD_SHA256:
        raise FCUjSemanticsRenderError("FCUj_ witness payload SHA-256 changed")
    try:
        payload.decode("ascii")
    except UnicodeDecodeError as error:
        raise FCUjSemanticsRenderError("FCUj_ witness payload is not ASCII") from error

    text = template.decode("utf-8")
    start_anchor = "def d7CoreWitnessChunks : Array String := #["
    end_anchor = "def d7CoreWitnessCharAt (index : Nat) : Char :="
    start = text.find(start_anchor)
    end = text.find(end_anchor)
    if start < 0 or end < 0 or end <= start:
        raise FCUjSemanticsRenderError("witness-table anchors changed")
    newline = "\r\n" if "\r\n" in text else "\n"
    witness_block = newline.join(
        (
            "def d7CoreWitnessPayload : String :=",
            "  include_str \"../../../../scripts/r45_d12_cover9_universal/"
            "MASTER7_R34_FCUJ_CORE_SEMANTIC_WITNESSES_V1.bin\"",
            "",
            "def d7CoreWitnessChunks : Array String := #[d7CoreWitnessPayload]",
            "",
            f"def d7CoreWitnessChunkSize : Nat := {PAYLOAD_CHARACTERS}",
            "",
        )
    )
    text = text[:start] + witness_block + text[end:]

    for old, new, expected in (
        ("R44Cover6Master7R34FgraveGow", "R44Cover6Master7R34FCUj", 4),
        ("fgraveGow", "fCUj", 15),
        ("F`GOW", "FCUj_", 1),
        ("5,807", "1,104", 1),
        ("3,227", "476", 2),
        ("2,396", "514", 2),
    ):
        text = _replace_literal(text, old, new, expected)

    for old, new, expected in (
        (5807, 1104, 10),
        (3227, 476, 21),
        (2396, 514, 37),
        (3395, 574, 3),
        (5791, 1088, 3),
        (168, 98, 7),
        (14058, PAYLOAD_CHARACTERS, 1),
    ):
        text = _replace_number(text, old, new, expected)

    forbidden = (
        "FgraveGow",
        "fgraveGow",
        "Fin 5807",
        "Fin 3227",
        "Fin 2396",
        "Fin 168",
        "d7CoreWitnessChunks : Array String := #[\n  \"",
    )
    leftovers = [token for token in forbidden if token in text]
    if leftovers:
        raise FCUjSemanticsRenderError(
            "stale template tokens remain: " + ", ".join(map(repr, leftovers))
        )
    return text.encode("utf-8")


def metadata(path: Path, payload: bytes) -> dict[str, object]:
    return {
        "name": path.name,
        "bytes": len(payload),
        "sha256": sha256_bytes(payload),
    }


def parse_cli(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("audit", "emit", "verify"), nargs="?", default="audit")
    parser.add_argument("--template", type=Path, default=TEMPLATE_PATH)
    parser.add_argument("--payload", type=Path, default=PAYLOAD_PATH)
    parser.add_argument("--output", type=Path, default=OUTPUT_PATH)
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> None:
    args = parse_cli(argv)
    rendered = render_module(args.template, args.payload)
    if args.command == "emit":
        try:
            with args.output.open("xb") as stream:
                stream.write(rendered)
        except FileExistsError:
            raise FileExistsError(f"refusing to overwrite generated module: {args.output}")
        status = "EMITTED_NEW_FCUJ_SEMANTICS_MODULE"
    elif args.command == "verify":
        if args.output.read_bytes() != rendered:
            raise FCUjSemanticsRenderError(
                "tracked FCUj_ semantics module differs from deterministic render"
            )
        status = "PASS_TRACKED_FCUJ_SEMANTICS_MODULE_EXACT"
    else:
        status = "PASS_FCUJ_SEMANTICS_MODULE_RENDER_AUDIT"
    print(json.dumps({"status": status, "artifact": metadata(args.output, rendered)}, indent=2))


if __name__ == "__main__":
    main()
