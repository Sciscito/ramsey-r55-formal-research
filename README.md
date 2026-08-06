# Formal research on `R(5,5)`

Private, reproducible research workspace for the exact diagonal Ramsey number
`R(5,5)`, combining Lean proofs, independently checked catalogue certificates,
SAT encodings and LRAT certificates.

> **Scientific status — 2026-08-06:** this repository does **not** prove
> `R(5,5)=43`. The currently verified public interval remains
> `43 ≤ R(5,5) ≤ 46`.

## Verified Lean/LRAT `R(4,4,16)` classification checkpoint

The right-hand catalogue needed by the degree-eight `R(4,5,25)` split is now
covered end to end in Lean. The terminal theorem is:

```lean
ramseyFree_isomorphic_to_gen4416
    (coloring : Nat → Bool)
    (hfree : isRamseyFree 16 4 4 coloring) :
    ∃ targetIndex,
      targetIndex < gen4416GraphIds.length ∧
        GraphIsomorphicFin (coloringGraph 16 coloring)
          (gen4416Graph targetIndex)
```

Thus every `(4,4)`-free coloring on sixteen vertices is strongly isomorphic
to one of the two materialized `gen4416` targets. The statement is a finite
cover by those two targets; it does not rely on, or claim, a separate formal
proof that the targets are non-isomorphic.

The proof composes the certified `R(3,4)` block catalogues, the exact
10,880-clause guarded CNF and its LRAT replay, a Lean semantics proof for the
four mixed-clique clause families, 64 checked mask-to-target permutations,
two checked self-complement permutations, and the unrooted/complement
reduction. `R44Gen4416TargetAudit` additionally proves that both materialized
targets satisfy the required `R(4,4)` graph predicate.

`R45DegreeEightGen4416Bridge` now composes this classification with the
certified `gen358` cover. Its theorem
`degree_eight_enters_gen358_and_gen4416` simultaneously returns a `gen358`
parent for the red eight-vertex block and a `gen4416` target for the
complemented blue sixteen-vertex block of every degree-eight `K25` branch.
The source SHA-256 is
`85B0DBF179D2DA759AA14D13E0834D788255E0B0F33003BDDD5937ABA4B031B5`.

This is an independent machine-verifiable Lean/LRAT certification, not a claim
of a first classification or a new mathematical result: McKay's
[Ramsey graph catalogue](https://users.cecs.anu.edu.au/~bdm/data/ramsey.html)
already lists two `R(4,4,16)` graphs, and Gauthier–Brown's
[*A Formal Proof of R(4,5)=25*](https://arxiv.org/abs/2404.01761) formalizes
the relevant enumeration and coverage in HOL4. A publication claim would
therefore require a sufficiently distinct contribution in proof architecture,
Lean/LRAT integration or certificate methodology. The result is **not** a new
Ramsey-number bound, a proof of `R(4,5) ≤ 25`, or progress by itself on the
exact value of `R(5,5)`.

## Verified catalogue foundation

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
- certified `R(4,5,25)` degree-eight prototype leaf `d8_l22_r01`: an
  8,352,876-byte LRAT trace is replayed against the exact 276-variable,
  55,154-clause reduced CNF;
- certified left cover for that degree-eight split: a generated table links
  all 179 representatives of the exhaustive Lean `R(3,5,8)` catalogue to the
  27 `gen358` parents, and
  `every_r35_order_eight_graph_enters_gen358` covers every arbitrary valid
  order-eight graph up to an explicit isomorphic completion;
- certified semantic split for every actual degree-eight `K25` branch:
  `degree_eight_local_split` sends the red block into `gen358`, constructs the
  exact sixteen-vertex blue block, and proves its complemented coloring is
  `R(4,4,16)`-free while relating it to the raw DIMACS convention;
- certified rooted `R(3,4)` subcatalogues: filtering the exhaustive `R(3,5)`
  catalogues leaves exactly 9 order-seven and 3 order-eight classes, with
  completeness modulo `GraphIsoFin` for the planned `gen4416` classifier;
- certified guarded `gen4416` classifier CNF: 83 variables and 10,880 clauses
  cover the 27 rooted block pairs after blocking 64 labelled masks; its
  3,658,365-byte LRAT is replayed by
  `r44_rooted_gen4416_classifier_unsat`;
- certified semantic `gen4416` composition: the four mixed `K4`/independent
  `4` families imply the exact generated CNF, all 64 allowed masks have
  checked permutations to a target, both targets have checked
  self-complement permutations, and
  `ramseyFree_isomorphic_to_gen4416` covers every arbitrary free coloring;
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
           LRATCatcher.Tests.R55DegreeBounds `
           LRATCatcher.Tests.R44RootedR34Catalogue `
           LRATCatcher.Tests.R44RootedGen4416Classifier `
           LRATCatcher.Tests.R44Gen4416TargetAudit `
           LRATCatcher.Tests.R44Gen4416Classification `
           LRATCatcher.Tests.R45DegreeEightCover `
           LRATCatcher.Tests.R45DegreeEightBridge `
           LRATCatcher.Tests.R45DegreeEightGen4416Bridge `
           LRATCatcher.Tests.R45DegreeEightPilot
```

Expected key theorems:

```text
r35_catalogue_order_ten_complete :
  StrongCatalogueComplete 10 (catalogues.getD 10 [])

ramseyFree_isomorphic_to_gen4416 :
  ∀ coloring, isRamseyFree 16 4 4 coloring →
    ∃ targetIndex, targetIndex < gen4416GraphIds.length ∧
      GraphIsomorphicFin (coloringGraph 16 coloring)
        (gen4416Graph targetIndex)

degree_eight_enters_gen358_and_gen4416
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8) :
    (∃ parentIndex, parentIndex < gen358ParentIds.length ∧
      CoveredByGen358Parent
        (redDegreeEightGraph coloring root hdegree)
        (gen358ParentIds.getD parentIndex 0)) ∧
      ∃ targetIndex, targetIndex < gen4416GraphIds.length ∧
        GraphIsomorphicFin
          (coloringGraph 16
            (blueDegreeSixteenColoring coloring root hroot hdegree))
          (gen4416Graph targetIndex)
```

The generated rooted data can be regenerated and checked independently with:

```powershell
python -m unittest scripts.r45_d8_pilot.test_gen4416_rooted_classifier `
  scripts.r45_d8_pilot.test_gen4416_rooted_proof_artifacts
python scripts\r45_d8_pilot\gen4416_rooted_classifier.py verify
```

Relevant SHA-256 values are:
`863C78226DDEFE17FEEF046F7F818D01ECFE63EE96663AEFEC1BE81EC591AAF4`
for the guarded CNF,
`786578E2E05E62E5B814BFC86656513E42A52D6467B190783637D6FC1AD33A61`
for its LRAT,
`1995924E5D942F437BF24A649A23EC9843A9375678DA8A044ABAD4FBF05E4670`
for the 64-row table and
`39A747796E2C3FE6FFB9CE2FDE541711A47487A035F4F0C7AB1981BA4243FAB3`
for the generated Lean cover data.

## Next formal objective

For the `R(4,5,25)` degree-eight split,
`degree_eight_enters_gen358_and_gen4416` now closes the existential
composition of both certified local covers. The next obligation begins at
transporting those two local isomorphisms into one block-preserving
permutation of `K25`, followed by the exact parent-unit bridge and replay of
the 53 remaining LRAT leaves. Completing those steps would turn the presently
experimental 54/54 UNSAT computation into a composed Lean theorem excluding
that root-degree case.

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

For the new classification, `#print axioms` shows no `sorryAx`. Its trust
boundary is the Lean kernel and standard classical/quotient axioms, plus the
explicit native bridges used for LRAT replay and finite `native_decide`
checks; consequently the native compiler/runtime are part of the practical
trusted base unless the certificates are replayed in kernel-only mode.
