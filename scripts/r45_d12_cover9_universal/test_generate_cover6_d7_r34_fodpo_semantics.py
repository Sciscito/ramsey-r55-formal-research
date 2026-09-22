from __future__ import annotations

import hashlib
import tempfile
import unittest
from pathlib import Path

from . import generate_cover6_d7_r34_fodpo_semantics as generator


class FoDPOSemanticsRendererTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.rendered = generator.render_module()

    def test_exact_render_identity_and_specialisation(self) -> None:
        self.assertEqual(
            hashlib.sha256(self.rendered).hexdigest().upper(),
            "5C41697844EB1CBB0C31A5F8F93F158407979A28973D637027623A419096FDC4",
        )
        source = self.rendered.decode("utf-8")
        for fragment in (
            "import LRATCatcher.Tests.R44Cover6Master7R34FoDPOCore",
            "namespace LRATCatcher.Tests.R44Cover6Master7R34FoDPOSemantics",
            "Fin foDPOCoreFinIndices.size",
            "position : Fin 7686",
            "position : Fin 183",
            "position : Fin 4221",
            "position : Fin 3264",
            "position : Fin 18",
            "dataLength d7CoreWitnessChunks = 18713",
            "MASTER7_R34_FODPO_CORE_SEMANTIC_WITNESSES_V1.bin",
            "theorem no_degreeSeven_foDPO_cover6_avoiding",
        ):
            self.assertIn(fragment, source)
        for stale in ("FgraveGow", "fgraveGow", "Fin 5807", "Fin 3227"):
            self.assertNotIn(stale, source)

    def test_tracked_module_is_the_exact_deterministic_render(self) -> None:
        self.assertEqual(generator.OUTPUT_PATH.read_bytes(), self.rendered)

    def test_template_mutant_is_rejected_before_rendering(self) -> None:
        original = generator.TEMPLATE_PATH.read_bytes()
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "mutated-template.lean"
            path.write_bytes(original.replace(b"Fin 5807", b"Fin 5808", 1))
            with self.assertRaisesRegex(
                generator.FoDPOSemanticsRenderError,
                "template SHA-256 changed",
            ):
                generator.render_module(path, generator.PAYLOAD_PATH)

    def test_payload_mutant_is_rejected_before_rendering(self) -> None:
        original = generator.PAYLOAD_PATH.read_bytes()
        mutant = bytes((original[0] ^ 1,)) + original[1:]
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "mutated-payload.bin"
            path.write_bytes(mutant)
            with self.assertRaisesRegex(
                generator.FoDPOSemanticsRenderError,
                "payload SHA-256 changed",
            ):
                generator.render_module(generator.TEMPLATE_PATH, path)


if __name__ == "__main__":
    unittest.main()
