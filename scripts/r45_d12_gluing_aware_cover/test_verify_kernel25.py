from __future__ import annotations

import ast
import itertools
import unittest

from . import verify_kernel25 as kernel


class KernelTwentyFiveCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = kernel.verify()

    def test_frozen_input_hashes_and_counts(self) -> None:
        self.assertEqual(kernel.sha256(kernel.KERNEL_PATH), kernel.EXPECTED_KERNEL_SHA256)
        self.assertEqual(kernel.sha256(kernel.COVER_PATH), kernel.EXPECTED_COVER_SHA256)
        self.assertEqual(self.report["status"], "PASS")
        recomputation = self.report["induced_recomputation"]
        self.assertEqual(recomputation["kernel_graphs_r44_checked"], 25)
        self.assertEqual(recomputation["four_vertex_subsets_per_kernel_graph"], 495)
        self.assertEqual(recomputation["four_vertex_subsets_checked"], 12_375)
        self.assertEqual(recomputation["subsets_per_kernel_graph"], 792)
        self.assertEqual(recomputation["induced_subgraphs_checked"], 19_800)

    def test_frozen_signature_hash_and_orbit_counts(self) -> None:
        recomputation = self.report["induced_recomputation"]
        self.assertEqual(
            tuple(recomputation["signature_sizes"]), kernel.EXPECTED_SIGNATURE_SIZES
        )
        self.assertEqual(
            recomputation["signature_sha256"], kernel.EXPECTED_SIGNATURE_SHA256
        )
        self.assertEqual(
            recomputation["canonical_motifs_in_kernel"],
            kernel.EXPECTED_CANONICAL_MOTIFS,
        )
        self.assertEqual(recomputation["s7_permutations"], 5_040)
        self.assertEqual(
            recomputation["s7_orbits_expanded"], kernel.EXPECTED_CANONICAL_MOTIFS
        )
        self.assertEqual(
            recomputation["labelled_masks_cached"],
            kernel.EXPECTED_LABELLED_MASKS_CACHED,
        )

    def test_exhaustive_lower_bound_and_frozen_cover(self) -> None:
        lower_bound = self.report["lower_bound"]
        self.assertFalse(lower_bound["hitting_set_found"])
        self.assertEqual(lower_bound["maximum_forbidden_size"], 4)
        self.assertEqual(lower_bound["dfs_states_explored"], kernel.EXPECTED_DFS_STATES)
        cover = self.report["frozen_five_motifs"]
        self.assertTrue(cover["all_kernel_graphs_hit"])
        self.assertEqual(
            tuple(cover["rows_hit_by_motif"]), kernel.EXPECTED_COVER_ROW_COUNTS
        )
        self.assertEqual(len(set(cover["canonical_graph6"])), 5)

    def test_graph6_roundtrip_and_strict_padding(self) -> None:
        for record in kernel.read_kernel(kernel.KERNEL_PATH):
            mask = kernel.decode_graph6_mask(record, 12)
            self.assertEqual(kernel.encode_graph6_mask(mask, 12), record)
        for record in kernel.read_cover(kernel.COVER_PATH):
            mask = kernel.decode_graph6_mask(record, 7)
            self.assertEqual(kernel.encode_graph6_mask(mask, 7), record)
        with self.assertRaisesRegex(ValueError, "padding"):
            kernel.decode_graph6_mask("F@h^h", 7)

    def test_canonicalization_is_s7_invariant(self) -> None:
        mask = kernel.decode_graph6_mask("F@h^g", 7)
        canonicalizer = kernel.OrderSevenCanonicalizer()
        canonical = canonicalizer.canonical(mask)
        for edge_map in canonicalizer.edge_maps[::719]:
            self.assertEqual(
                canonicalizer.canonical(kernel.relabel_mask(mask, edge_map)), canonical
            )

    def test_hitting_search_agrees_with_bruteforce_on_small_instances(self) -> None:
        instances = (
            ((0, 1), (1, 2), (2, 3)),
            ((0,), (1,), (2,)),
            ((0, 1, 2), (0, 3), (1, 3), (2, 3)),
        )
        for signatures in instances:
            candidates = sorted(
                {candidate for signature in signatures for candidate in signature}
            )
            for limit in range(4):
                brute = any(
                    all(set(chosen).intersection(row) for row in signatures)
                    for size in range(limit + 1)
                    for chosen in itertools.combinations(candidates, size)
                )
                found, _states = kernel.find_hitting_set(signatures, limit)
                self.assertEqual(found is not None, brute)

    def test_verifier_has_no_project_imports(self) -> None:
        tree = ast.parse(kernel.KERNEL_PATH.with_name("verify_kernel25.py").read_text())
        imported = {
            alias.name
            for node in ast.walk(tree)
            if isinstance(node, ast.Import)
            for alias in node.names
        }
        imported.update(
            node.module or ""
            for node in ast.walk(tree)
            if isinstance(node, ast.ImportFrom)
        )
        self.assertFalse(
            any(name == "scripts" or name.startswith("scripts.") for name in imported)
        )


if __name__ == "__main__":
    unittest.main()
