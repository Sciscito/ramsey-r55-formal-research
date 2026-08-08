from __future__ import annotations

import hashlib
import itertools
import json
import os
import unittest
from pathlib import Path

from . import analyze_master8_core_taxonomy as taxonomy
from . import certify_cover6_conditioned_orbit_witnesses as certificate
from . import certify_cover6_cube_motif_bridge as bridge
from . import exact_replay_cover6_d8 as replay


class Cover6ConditionedOrbitWitnessTests(unittest.TestCase):
    @classmethod
    def tracked(cls) -> dict[str, object]:
        return json.loads(
            Path(certificate.__file__).with_name(certificate.REPORT_NAME).read_text(
                encoding="utf-8"
            )
        )

    def test_little_endian_base64_round_trip_and_rejections(self) -> None:
        for value in (0, 1, 63, 64, 4095, 4096, 30_239, (1 << 18) - 1):
            encoded = certificate.encode_base64_le(value, 3)
            self.assertEqual(len(encoded), 3)
            self.assertEqual(certificate.decode_base64_le(encoded), value)
        with self.assertRaises(certificate.ConditionedWitnessError):
            certificate.encode_base64_le(1 << 18, 3)
        with self.assertRaises(certificate.ConditionedWitnessError):
            certificate.decode_base64_le("00+")
        with self.assertRaises(certificate.ConditionedWitnessError):
            certificate.decode_witness_code(30_240)

    def test_dense_fifteen_bit_stream_uses_five_characters_per_pair(self) -> None:
        witnesses = ((0, 0), (5, 5039), (2, 1729), (4, 7))
        payload = certificate.pack_witnesses(witnesses)
        self.assertEqual(len(payload), 10)
        self.assertEqual(certificate.unpack_witnesses(payload, 4), witnesses)
        self.assertEqual(certificate.witness_at(payload, 2, 4), witnesses[2])
        with self.assertRaises(certificate.ConditionedWitnessError):
            certificate.witness_at(payload, 4, 4)

    def test_lehmer_rank_is_exact_itertools_order(self) -> None:
        for rank, permutation in enumerate(itertools.permutations(range(7))):
            self.assertEqual(certificate.permutation_rank(permutation), rank)
            self.assertEqual(certificate.permutation_unrank(rank), permutation)
        with self.assertRaises(certificate.ConditionedWitnessError):
            certificate.permutation_rank((0, 1, 2, 3, 4, 5, 5))
        with self.assertRaises(certificate.ConditionedWitnessError):
            certificate.permutation_unrank(5040)

    def test_identity_witnesses_reconstruct_all_six_representatives(self) -> None:
        self.assertEqual(certificate.permutation_unrank(0), tuple(range(7)))
        for representative_index, cube in enumerate(replay.CUBE_REPRESENTATIVES):
            self.assertEqual(
                certificate.verify_cube_witness(cube, (representative_index, 0)),
                (representative_index, 0),
            )
            self.assertEqual(certificate.decode_cube(certificate.encode_cube(cube)), cube)

    def test_wrong_representative_mutant_is_rejected(self) -> None:
        cube = replay.CUBE_REPRESENTATIVES[0]
        with self.assertRaises(certificate.ConditionedWitnessError):
            certificate.verify_cube_witness(cube, (1, 0))
        with self.assertRaises(certificate.ConditionedWitnessError):
            certificate.verify_cube_witness(cube, (-1, 0))
        with self.assertRaises(certificate.ConditionedWitnessError):
            certificate.verify_cube_witness(cube, (0, -1))

    def test_positional_order_swap_mutant_is_rejected(self) -> None:
        cubes = replay.CUBE_REPRESENTATIVES[:2]
        ordered = certificate.pack_witnesses(((0, 0), (1, 0)))
        self.assertEqual(
            certificate.unpack_witnesses(ordered, 2), ((0, 0), (1, 0))
        )
        swapped = certificate.pack_witnesses(((1, 0), (0, 0)))
        with self.assertRaises(certificate.ConditionedWitnessError):
            certificate.verify_cube_witness(
                cubes[0], certificate.witness_at(swapped, 0, 2)
            )

    def test_wrong_projected_lift_mutant_is_rejected(self) -> None:
        representative = replay.CUBE_REPRESENTATIVES[0]
        compatible_counts = [
            count for count in range(7)
            if bridge.compatible_with_root(representative, count)
        ]
        self.assertTrue(compatible_counts)
        count = compatible_counts[0]
        projected = (
            replay.project_nonroot(representative[0]),
            replay.project_nonroot(representative[1]),
        )
        witness, full = certificate.verify_projected_lift_witness(
            projected, count, (0, 0)
        )
        self.assertEqual(witness, (0, 0))
        self.assertEqual(full, representative)
        with self.assertRaises(certificate.ConditionedWitnessError):
            certificate.verify_projected_lift_witness(projected, count, (1, 0))

    def test_actual_indexed_source_payloads_have_frozen_bytes(self) -> None:
        block, local = certificate.indexed_source_payloads()
        self.assertEqual(len(block), 32_880 * 7)
        self.assertEqual(len(local), 1_200 * 7)
        self.assertEqual(
            hashlib.sha256(block.encode("ascii")).hexdigest().upper(),
            certificate.BLOCK_CUBE_PAYLOAD_SHA256,
        )
        self.assertEqual(
            hashlib.sha256(local.encode("ascii")).hexdigest().upper(),
            certificate.LOCAL_CUBE_PAYLOAD_SHA256,
        )
        self.assertEqual(
            certificate.decode_cube(block[:7]),
            (0x000048, 0x07DEDE),
        )
        self.assertEqual(
            certificate.decode_cube(local[:7]),
            (0x000000, 0x002F4F),
        )
        # Preserve positional order, not merely the set of decoded cubes: an
        # adjacent-record transposition keeps length/content multiplicities but
        # must fail the frozen payload identity check.
        reordered = block[7:14] + block[:7] + block[14:]
        with self.assertRaises(certificate.ConditionedWitnessError):
            certificate.require_exact_cube_payload(
                reordered,
                32_880,
                certificate.BLOCK_CUBE_PAYLOAD_SHA256,
                "mutated K7",
            )

    def test_actual_lean_core_index_order_matches_taxonomy(self) -> None:
        observed = certificate.indexed_source_core_master_indices()
        expected = tuple(row.master_id - 1 for row in taxonomy.core_rows())
        self.assertEqual(len(observed), 6_152)
        self.assertEqual(observed, expected)
        normalized = tuple(
            certificate.normalized_index_of_master(index) for index in observed
        )
        self.assertEqual(
            certificate.digest_lines(f"{index}\n" for index in normalized),
            "2C8839FD8B3E3CC949F4A5A4E09D2C7F522FBCCF072F32FC8EFBAD6553D7E89F",
        )

    def test_tracked_report_freezes_compact_honest_certificate(self) -> None:
        report = self.tracked()
        self.assertEqual(
            report["status"], "PASS_EXACT_CONDITIONED_ORBIT_WITNESSES"
        )
        self.assertEqual(
            report["source_payloads"]["full_k7_conditioned_cubes"]["sha256"],
            certificate.BLOCK_CUBE_PAYLOAD_SHA256,
        )
        self.assertEqual(
            report["source_payloads"]["projected_k6_conditioned_cubes"]["sha256"],
            certificate.LOCAL_CUBE_PAYLOAD_SHA256,
        )
        self.assertEqual(report["encoding"]["bits_per_witness"], 15)
        self.assertEqual(report["encoding"]["logical_bytes_per_witness"], 1.875)
        self.assertEqual(report["compression"]["total_entries"], 34_080)
        self.assertEqual(
            report["compression"]["witness_ascii_characters"], 85_200
        )
        self.assertEqual(report["compression"]["packed_logical_bytes"], 63_900)
        self.assertTrue(
            report["projected_k6_canonical_lift_orbit_witnesses"]
            ["all_full_lifts_unique_within_reduced_cube_family"]
        )
        self.assertTrue(report["lean_integration_boundary"]["not_yet_a_lean_theorem"])
        self.assertIn("no SAT, LRAT", report["scope"])
        core = report["normalized_core_specific_ordered_view"]
        self.assertEqual(
            (core["retained_full_k7_blockers"], core["retained_projected_k6_blockers"]),
            (3_514, 2_409),
        )
        self.assertEqual(
            core["combined_core_ordered_view_sha256"],
            "D0B25A635706B12B45757774060450B55EB5346F5C1E36E2CCFDA29A571D4058",
        )
        self.assertFalse(core["additional_payload_required"])

    def test_tracked_witness_chunks_have_exact_lengths_and_hashes(self) -> None:
        report = self.tracked()
        payloads = report["certificate_payloads"]
        block = "".join(payloads["full_k7_witness_chunks"])
        local = "".join(payloads["projected_k6_lift_witness_chunks"])
        self.assertEqual(len(block), 32_880 * 15 // 6)
        self.assertEqual(len(local), 1_200 * 15 // 6)
        self.assertEqual(
            certificate.sha256_ascii(block),
            report["full_k7_orbit_witnesses"]["sha256"],
        )
        self.assertEqual(
            certificate.sha256_ascii(local),
            report["projected_k6_canonical_lift_orbit_witnesses"]["sha256"],
        )
        # Decoding all 34,080 bit-packed records is cheap and catches malformed,
        # out-of-range, or noncanonical payload data without regenerating cubes.
        for representative, permutation in certificate.unpack_witnesses(block, 32_880):
            self.assertLess(representative, 6)
            self.assertLess(permutation, 5040)
        for representative, permutation in certificate.unpack_witnesses(local, 1_200):
            self.assertLess(representative, 6)
            self.assertLess(permutation, 5040)

    @unittest.skipUnless(
        os.environ.get("RAMSEY_COVER6_CONDITIONED_WITNESSES_FULL") == "1",
        "set RAMSEY_COVER6_CONDITIONED_WITNESSES_FULL=1 for all 34,080 rows",
    )
    def test_full_regeneration_and_mutant_detection(self) -> None:
        generated = certificate.build_report()
        tracked = self.tracked()
        self.assertEqual(generated, tracked)

        sections = certificate.block_catalogue_sections()
        first_cube = sections[0][1][0]
        payload = "".join(
            tracked["certificate_payloads"]["full_k7_witness_chunks"]
        )
        records = list(certificate.unpack_witnesses(payload, 32_880))
        certificate.verify_cube_witness(first_cube, records[0])
        representative, permutation = records[0]
        mutant = ((representative + 1) % 6, permutation)
        with self.assertRaises(certificate.ConditionedWitnessError):
            certificate.verify_cube_witness(first_cube, mutant)

        second_cube = sections[0][1][1]
        records[0], records[1] = records[1], records[0]
        reordered = certificate.pack_witnesses(tuple(records))
        with self.assertRaises(certificate.ConditionedWitnessError):
            certificate.verify_cube_witness(
                first_cube, certificate.witness_at(reordered, 0, 32_880)
            )
        with self.assertRaises(certificate.ConditionedWitnessError):
            certificate.verify_cube_witness(
                second_cube, certificate.witness_at(reordered, 1, 32_880)
            )


if __name__ == "__main__":
    unittest.main()
