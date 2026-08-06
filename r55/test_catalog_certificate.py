import itertools
from copy import deepcopy
from pathlib import Path
import unittest

from catalog_certificate import (
    extend_graph,
    find_isomorphism,
    generate_certificate,
    is_isomorphism,
    is_r35_free,
    verify_certificate,
)
from ramsey import decode_graph6


def cycle_graph(n):
    rows = [0] * n
    for vertex in range(n):
        neighbor = (vertex + 1) % n
        rows[vertex] |= 1 << neighbor
        rows[neighbor] |= 1 << vertex
    return tuple(rows)


class CatalogueCertificateTests(unittest.TestCase):
    def test_extension_and_property(self):
        c5 = cycle_graph(5)
        self.assertTrue(is_r35_free(extend_graph(c5, 0)))
        self.assertFalse(is_r35_free(extend_graph(c5, 0b11)))
        self.assertTrue(is_r35_free(c5))

    def test_isomorphism_finder_on_all_c5_relabellings(self):
        c5 = cycle_graph(5)
        for permutation in itertools.permutations(range(5)):
            relabelled = tuple(
                sum(
                    1 << permutation[neighbor]
                    for neighbor in range(5)
                    if (c5[vertex] >> neighbor) & 1
                )
                for vertex in sorted(range(5), key=permutation.__getitem__)
            )
            found = find_isomorphism(c5, relabelled)
            self.assertIsNotNone(found)
            self.assertTrue(is_isomorphism(c5, relabelled, found))

    def test_nonisomorphic_graphs_are_rejected(self):
        empty4 = decode_graph6("C?")
        path4 = decode_graph6("Ch")
        self.assertIsNone(find_isomorphism(empty4, path4))

    def test_bad_permutation_is_rejected(self):
        c5 = cycle_graph(5)
        self.assertFalse(is_isomorphism(c5, c5, (0, 0, 1, 2, 3)))

    def test_small_certificate_and_mutations(self):
        directory = Path(__file__).resolve().parent
        certificate = generate_certificate(directory, 4)
        self.assertEqual(
            verify_certificate(certificate, directory),
            {"max_order": 4, "catalogue_graphs": 14, "valid_extensions": 29},
        )

        missing = deepcopy(certificate)
        missing["transitions"][3]["records"].pop()
        with self.assertRaisesRegex(ValueError, "missing valid extension"):
            verify_certificate(missing, directory)

        corrupt = deepcopy(certificate)
        corrupt["transitions"][3]["records"][0][3] = [0, 0, 1, 2]
        with self.assertRaisesRegex(ValueError, "invalid isomorphism"):
            verify_certificate(corrupt, directory)


if __name__ == "__main__":
    unittest.main()
