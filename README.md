# Formal research on `R(5,5)`

Private, reproducible research workspace for the exact diagonal Ramsey number
`R(5,5)`, combining Lean proofs, independently checked catalogue certificates,
SAT encodings and LRAT certificates.

> **Scientific status — 2026-08-06:** this repository does **not** prove
> `R(5,5)=43`. The currently verified public interval remains
> `43 ≤ R(5,5) ≤ 46`.

## Main verified milestone

The semantic exhaustiveness of the generated `R(3,5,n)` catalogues is now
proved in Lean through order 10:

```lean
r35_catalogues_complete :
  ∀ order, order ≤ extensionWitnesses.length →
    StrongCatalogueComplete order (catalogues.getD order [])

r35_catalogue_order_ten_complete :
  StrongCatalogueComplete 10 (catalogues.getD 10 [])

d20c10_type_covered_by_orderTenCatalogue :
  ∃ representative ∈ catalogues.getD 10 [],
    GraphIsomorphicFin branch.typeGraph representative
```

The proof covers last-vertex decomposition, parent and mask validity,
neighbourhood-mask transport through a finite permutation, invariance of the
executable graph predicate, checked catalogue transitions and composition of
strong graph isomorphisms. There are no `sorry` or `admit` placeholders.

## Other verified results

- compact certified upper bound `R(4,4) ≤ 18`: a 961,008-byte LRAT proof
  establishes `R(3,4) ≤ 9`, then `RamseyRecurrence.lean` proves the classical
  red/blue recurrence semantically in Lean;
- conditional global degree theorem `allDegrees_le_twentyFour`: from
  `R(4,5) ≤ 25`, every vertex of a hypothetical `K43` counterexample has
  both red and blue degree at most 24;
- explicit 42-vertex witness checked by Lean, hence `R(5,5) ≥ 43`;
- canonical `K43` encoding: 903 variables and 1,925,196 clauses;
- 1,509 tight structural branches;
- all 313 types in the `d=20,c=10` layer are solver-UNSAT;
- two LRAT leaves replayed in Lean, including the difficult `t312 = W5` leaf;
- 912 catalogue graphs, 206,003 candidate extensions and 8,989 valid checked
  extensions;
- W5 symmetry check: 320 automorphisms, 1,024 signatures and 39 orbits;
- semantic Lean bridge from every exact `d=20,c=10` common neighbourhood to
  one of the certified order-10 catalogue representatives;
- canonical Lean constructor `LocalD20C10Witness.package`: from the three
  local facts `degree(root)=20`, `anchor ∈ N(root)` and
  `codegree(root,anchor)=10`, it builds the exact lists and packed induced
  graph consumed by that bridge;
- canonical-label specialization
  `canonicalBranch_covered_by_orderTenCatalogue`, reducing the local branch
  to the two exact equalities `N(0)=[1,…,20]` and
  `N(0)∩N(1)=[2,…,11]`;
- audited DIMACS semantics bridge `R55CanonicalUnitsBridge.lean`: the 42 root
  units and 19 anchor units, including the one-based DIMACS to zero-based Lean
  shift, imply those exact equalities and therefore certified catalogue
  coverage;
- exact index bridge `R55CanonicalCommonIndex.lean`: local vertex `i : Fin 10`
  is global vertex `i+2`, and every induced-graph bit is the corresponding
  ambient Ramsey edge;
- exact 45-literal type bridge `R55TypedUnitsBridge.lean`: satisfaction of
  `fixed_anchor_type_clauses` is equivalent to literal equality between the
  canonical induced packed graph and the selected order-10 catalogue type;
- concrete kernel proof that zero-based type index `312` is the W5 graph used
  by the hard symmetry-certified branch;
- full vertex-permutation invariance `R55ColoringPermutation.lean`: relabeling
  all 43 vertices preserves `isRamseyFree 43 5 5` in both directions, using
  an exhaustively checked decoder for the 903 edge variables;
- constructive WLOG `R55CanonicalRelabeling.lean`: every exact local
  degree-20/codegree-10 witness yields a genuine permutation of all 43
  vertices, a globally relabeled Ramsey-free coloring, and satisfaction of
  the 61 canonical root/anchor units;
- exact type-0 leaf decomposition in `R55MinLeafBridge.lean` and
  `R55MinLeafSemantics.lean`: the 2,047,379-clause certified CNF is split into
  its Ramsey, two auxiliary-counter, and 106 unit clauses; contradiction is
  proved from the semantic branch plus explicit satisfaction of the two
  counter blocks, without claiming their soundness prematurely;
- 37 Python tests.

## Repository layout

- `r55/`: deterministic Python generators, tests, graph6 catalogues,
  certificates and search journals;
- `vendor/lrat-catcher/`: LRAT-Catcher plus the local Lean development;
- `docs/`: complete checkpoint guide, manifest and restart prompt;
- `STATUS.md`: current scientific report;
- `ARTIFACTS.md`: hashes and retrieval instructions for the large proof files;
- `scripts/verify-source.ps1`: source-level Python and Lean smoke test.

The full 82.6 MiB portable checkpoint, including the large CNF/LRAT pairs and
Windows verification tools, is attached to the private GitHub Release
[`checkpoint-2026-08-06`](../../releases/tag/checkpoint-2026-08-06).

## Quick verification

Requirements: Python 3.12+, Elan, Lean 4.30.0 and Lake.

```powershell
Set-ExecutionPolicy -Scope Process Bypass
.\scripts\verify-source.ps1
```

Direct Lean integration check:

```powershell
cd vendor\lrat-catcher
lake build LRATCatcher.Tests.R35CatalogCheckpoint `
           LRATCatcher.Tests.R55W5Symmetry `
           LRATCatcher.Tests.R55CommonNeighborhoodBridge `
           LRATCatcher.Tests.R55CanonicalUnitsBridge `
           LRATCatcher.Tests.R55CanonicalCommonIndex `
           LRATCatcher.Tests.R55TypedUnitsBridge `
           LRATCatcher.Tests.R55ColoringPermutation `
           LRATCatcher.Tests.R55CanonicalRelabeling `
           LRATCatcher.Tests.RamseyUpperBounds `
           LRATCatcher.Tests.R55DegreeBounds
```

Expected final theorem:

```text
r35_catalogue_order_ten_complete :
  StrongCatalogueComplete 10 (catalogues.getD 10 [])
```

## Next formal objective

The canonical local-graph construction, DIMACS unit-clause soundness bridge
and WLOG relabeling are complete once an exact local degree-20/codegree-10
witness is supplied. The global degree bound is also formal, conditional on
the still-missing certificate `R(4,5) ≤ 25`. Direct monolithic runs are
quantified in [RAMSEY_BOUND_DIAGNOSTICS.md](RAMSEY_BOUND_DIAGNOSTICS.md) and
show that the next attempt should use symmetry breaking or a checked cube
cover. Remaining obligations include deriving and covering the
required local witnesses from every global branch, certifying that each
external graph6/manifest index denotes the same packed Lean catalogue entry,
the global degree/codegree reduction, soundness of the two type-0 counter
encodings, regularity and
lexicographic symmetry constraints, and compositional LRAT coverage of every
leaf.

See [docs/GUIDE_REPRISE.md](docs/GUIDE_REPRISE.md) for exact environment,
commands, hashes and trust-base caveats.
