# Formal research on `R(5,5)`

## Research update - later 2026-08-07

This update supersedes the earlier 7/13 cover6 and 1,509 active-branch
counts retained below as historical checkpoint detail.

- The complement-closed cover6 degree-eight split is now generated for all
  13 two-centre cases. A standalone deterministic reimplementation now checks
  all `2^21` local assignments, reconstructs the ordered 3,367,437-clause
  source byte for byte, and separately executes simplification,
  deduplication and insertion of the 21 units for all 13 residuals. Every
  frozen residual agrees byte for byte. This closes the finite CNF audit, not
  the mathematical theorem: CaDiCaL returns `UNSAT_WITHOUT_PROOF` on 13/13
  cases (58--3,073 conflicts), but no cover6 LRAT or Lean composition is
  claimed.
- The exact universal statement, polarity convention and remaining semantic
  gaps are frozen in
  `docs/R44_COVER6_D8_SEMANTIC_TARGET_2026-08-07.md`. A deliberately small
  `R(3,3,5)`/induced-`P3` analogue now closes the complete declarative
  encoding -> DIMACS -> LRAT -> Lean chain, including negative mutation
  tests. This is a level-4 result for the toy theorem only.
- Lean now materializes the six exact cover6 graph6 records, checks the three
  complement pairs, and proves that a full 21-literal DIMACS blocker is false
  exactly on an induced labelled occurrence. The remaining bridge is the
  expansion of the conditioned partial cubes into the global source and its
  composition with the two-centre branches.
- The published extremal R(4,5,20) classification makes the
  minimum-anchor layer d=20,c=10 empty before SAT: minimum degree 10 would
  force a 10-regular 100-edge graph, while the unique published extremal
  class has degree sequence 9^2 10^16 11^2. This removes 313 branches:
  K43: 1,509 -> 1,196 and the new K45 skeleton 1,815 -> 1,502.
- A bounded eight-leaf screen of the remaining K43 space produced one
  proof-free UNSAT and seven UNKNOWN results at 100,000 conflicts. Raising
  budgets is therefore not the next strategy.
- An exclusive-neighbourhood lemma places a block of size `q=d-1-c` in
  `R(4,4,q)`. Frozen local copies of the official order-10 and order-11
  catalogues admit explicit augmented order-seven motif covers. An independent
  implementation rechecked every source graph and every declared cover,
  yielding a catalogue-relative K45 architecture with 112 motif obligations
  (126 when complement closure is imposed), instead of 1,502 typed cases. No
  SAT obligation is closed and no universal or formal K45 reduction is claimed.
- The K45 excess identity yields useful near-extremal-neighbourhood
  constraints but eliminates no degree by itself.

Exact tracked summaries are
r55/K43_SCREEN_2026-08-07.json,
scripts/r45_d12_cover9_universal/COVER6_D8_CHECKPOINT13.json,
scripts/r45_d12_cover9_universal/COVER6_D8_SEMANTIC_REPLAY_V1.json, and
docs/R45_D20_C10_MINIMUM_ANCHOR_VACUITY_2026-08-07.md.
The structural pilot is documented in
docs/R45_EXCLUSIVE_R44_MOTIF_QUOTIENT_2026-08-07.md.
No new Ramsey-number bound is claimed.

Private, reproducible research workspace for the exact diagonal Ramsey number
`R(5,5)`, combining Lean proofs, independently checked catalogue certificates,
SAT encodings and LRAT certificates.

> **Scientific status — 2026-08-07:** this repository does **not** prove
> `R(5,5)=43`. The currently verified public interval remains
> `43 ≤ R(5,5) ≤ 46`.

## Degree-twelve research checkpoint

The red-degree-twelve branch of `R(4,5,25)` has a compiled semantic scaffold,
but it is **not closed**. Lean constructs the exact `1 + 12 + 12` global
relabeling, selects one of the twelve exhaustive `R(3,5,12)` types, proves
the 66 left-block units, and handles partial right-block patterns with both
raw and complemented polarities explicit. The 280-variable, 54,638-clause
guarded formula closes its four invalid selector codes, but still closes
**0/12 mathematical selector cases**.

The strongest new finite result is an exact minimum complement-closed cover
of the frozen `r44_12.g6` catalogue by six order-seven motifs, arranged as
three exact complement pairs. The records are `F@h^g`/`FKDhw`,
``FG`Xo``/`FdW}w`, and `FHFLw`/`FIIXw`. A direct standard-library
verifier reads all 1,449,166 order-twelve records and checks all 792
seven-subsets per record, obtaining zero holes without reading the discovery
incidence matrix or a witness file. An independent 30-graph kernel excludes
every choice of at most two complement pairs after reconstructing all `2^21`
labelled order-seven graphs, the 923,012 valid `R(4,4)` graphs, and all 181
complement pairs. Thus the minimum is exactly three pairs, or six motif
classes, for the frozen catalogue. This statement remains explicitly
**catalogue-relative** until catalogue completeness is connected to a
proof-independent universal argument.

The six-record cover has SHA-256
`404E49E3218424FCB73314ADEE42CC873CD3F8D67E4615653A8BC0210F61AD16`;
its labelled closure contains 25,200 masks and has SHA-256
`04B9688924BFC2EF6F92FB5734B19E7E771C37446DD3E442ECED8648BE1CBDD7`;
the 30-graph kernel has SHA-256
`EB61306B5DA0F15DC1112D82007BB29CD2FD3AEE460FD1C0D62E24401C66C8CC`.
The earlier unrestricted order-seven minimum remains five, with cover SHA
`CEAE61F737722C6D1392B5C8D654FC1B09D482AA3C76222EE2D9CBFF3CA5E288`
and no-cover4 LRAT SHA
`4FD1F02297F5019B9EADBE9BC20E29DF326B0B7F99B8A539C140FD9911F15793`.

The catalogue-independent universal `cover9` target has advanced from
solver evidence to exact certification for root degree eight. Its 13
exhaustive two-centre residual CNFs all have CaDiCaL LRAT refutations
independently replayed by LRAT-Catcher/Lean. The 13 proofs total 222,740,623
bytes on `S:`; their portable manifest has SHA-256
`77FE47B5BC73865EDB0405DFC2D3B0A367C2A757B27A83CDC981D5958F80DE23`.
Lean separately formalizes the root permutation, degree bounds, two-centre
normalization and the exact 13-case disjunction. What remains is the semantic
bridge from the generated residual CNFs to motif avoidance, composition with
the 13 replay theorems, and the other root degrees.

The complement-closed cover6 supplies a sharper universal route: complement
symmetry reduces degrees `3..8` to representatives `6,7,8`. Two independent
implementations exhaust all `2^21` local assignments and agree on 25,200
syntactically complement-closed partial cubes (SHA-256
`0239E74AC009B28173E59C3293F7F9C9370A99832B19BB28205EF449E6238F7D`).
The predicted conditioned `K_12` formula sizes are 4,858,890, 4,312,419 and
3,367,437 clauses for degrees 6, 7 and 8 respectively. A historical checkpoint
called the degree-eight source formula "independently verified twice"; the
later audit showed that this was too strong. That concrete gap is now closed
by a separate deterministic code path: it reconstructs the ordered source,
recomputes all 13 reductions and compares every DIMACS byte. The tracked
report has SHA-256
`5D8D129A2431B7F473AF24B4BE21864FA6CCBE05DB4D347665FCE0749EB35024`.
The implementation deliberately shares the frozen representatives and
expected hashes, so it is not described as a low-common-mode independent
derivation. All 13 residuals return proof-free UNSAT. No cover6 LRAT exists,
and this is not yet an UNSAT theorem.

Accordingly the global progress count is still **0/12 complete degree-twelve
mathematical cases**, and no new Ramsey-number bound is claimed. The cover6
minimum and solver checkpoint are research leads; the exact-CNF audit is now
acquired, while the graph/DIMACS/Lean composition, certified UNSAT and broader
literature review remain required before any novelty or breakthrough claim. See
`docs/NEXT_CONVERSATION_HANDOFF_2026-08-07.md` for the precise restart state
and `docs/R45_D12_STRUCTURAL_COVER9_2026-08-07.md` for the structural audit.

## Verified Lean/LRAT red-degree-eight branch of `R(4,5,25)`

The red-degree-eight root case is now closed end to end in Lean. The terminal
theorem is:

```lean
no_root_has_redDegree_eight_certified
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring) :
    ∀ root, root < 25 →
      (colorNeighbors coloring root false).length ≠ 8

certified_exists_red_degree_ten_or_twelve
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring) :
    ∃ root, root < 25 ∧
      ((colorNeighbors coloring root false).length = 10 ∨
       (colorNeighbors coloring root false).length = 12)
```

`R45DegreeEightGuardedMasterSemantics` reconstructs a shared guarded formula
with 282 variables and 55,926 clauses and proves that its unsatisfiability
implies all 54 admissible `gen358 × gen4416` pair contradictions.
`R45DegreeEightGuardedMaster` replays a checked 59-cube cover—54 valid pairs
and five invalid selector-code blockers—using 59 trimmed LRAT leaf proofs and
one cover proof. It then checks the parsed CNF against the Lean decomposition
clause for clause and composes the result with the certified catalogue,
permutation and unit bridges. The targeted terminal build completed 56/56
with no `sorryAx`.

`R45RemainingDegrees` then composes this theorem with the already-certified
handshaking reduction to `{8, 10, 12}`. Its checked global consequence is that
every hypothetical `(4,5)`-free coloring of `K25` has a vertex of red degree
exactly 10 or 12. Thus only those two structural branches remain for the full
upper-bound proof.

This closes one structural root-degree branch only. It is **not** a proof of
`R(4,5) ≤ 25`, does not settle the other possible root degrees, and is not a
claim of new mathematics: the corresponding global result was already
formalized in HOL4 by Gauthier–Brown. The independently replayed Lean/LRAT
architecture and certificate composition are the contributions being tested.

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
proved in Lean through order 14 (with order 10 extracted for the `R(5,5)` work):

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
  8,352,876-byte LRAT trace is trimmed at elaboration time and replayed against
  the exact 276-variable, 55,154-clause reduced CNF;
- end-to-end semantic closure of that same leaf: the reduced Ramsey clauses,
  the two root-induced local blocks and all 148 parent units are identified
  clause-for-clause, and `no_degreeEight_l22r01_of_catalogue_witnesses`
  derives contradiction for every degree-eight branch carrying exactly the
  `gen358` parent-22 and `gen4416` target-1 witnesses;
- block-preserving `K25` relabeling and raw-color/unit bridges: the source now
  constructs a genuine global permutation fixing the root, transports the
  complemented `gen4416` classification back to the raw DIMACS polarity and
  proves literal-level satisfaction of both local unit blocks;
- generic 54-leaf semantic factorization:
  `catalogueWitnesses_leafAssembly` accepts arbitrary admissible parent/target
  indices and their catalogue witnesses, then returns the canonical ambient
  permutation together with satisfaction of the concatenated unit cube;
- certified guarded-master closure of all 54 local pairs: the shared
  282-variable, 55,926-clause CNF is covered by 59 checked cubes and its
  unsatisfiability proves `AllAdmissibleDegreeEightPairsContradictory`;
- unconditional degree-eight branch composition:
  `no_root_has_redDegree_eight_certified` proves that no root has red degree 8
  in a `(4,5)`-free coloring of `K25`, with no certificate-facing hypothesis
  left in the statement;
- certified two-branch global reduction:
  `certified_exists_red_degree_ten_or_twelve` combines handshaking parity, the
  checked `7..13` degree window and the degree-eight exclusion, leaving only
  red root degrees 10 and 12 in any hypothetical counterexample;
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

The 82.6 MiB portable checkpoint for the preceding milestone, including the
large CNF/LRAT pairs and Windows verification tools, is attached to the private
GitHub Release
[`checkpoint-2026-08-06`](../../releases/tag/checkpoint-2026-08-06). Its
manifest predates the guarded-master closure. The 59 leaf LRAT files and cover
proof are stored outside Git behind the ignored
`scripts/r45_d8_pilot/guarded_master/proofs/` junction. Four ZIP64 parts
(647,326,949 compressed bytes) have now been packed and independently verified;
their exact hashes and the SSD-first install procedure are recorded in
`ARTIFACTS.md`. The planned Release tag is
`r45-d8-guarded-master-lrat-v1`; portability remains pending until those four
assets are uploaded and redownloaded from GitHub successfully.

## Quick verification

Requirements: Python 3.12+, Elan, Lean 4.30.0 and Lake.

```powershell
Set-ExecutionPolicy -Scope Process Bypass
.\scripts\verify-source.ps1
```

The script checks the recorded SHA-256 values of the external `l22/r01`
CNF/LRAT pair before invoking Lake, so a cached `.olean` cannot mask a changed
certificate file. The terminal guarded-master target additionally requires the separately
materialized 59-leaf proof bundle. `proof_bundle.py` verifies or installs the
four archive parts into an explicit external cache; a fresh clone does not yet
retrieve the pending GitHub Release assets automatically. Verification is
strict by default; `-AllowMissingGuardedProofBundle` is an explicit source-only
smoke-test opt-out and is not a publication gate.

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
           LRATCatcher.Tests.R45DegreeEightGlobalPermutation `
           LRATCatcher.Tests.R45DegreeEightRawGen4416Bridge `
           LRATCatcher.Tests.R45DegreeEightGen358UnitsBridge `
           LRATCatcher.Tests.R45DegreeEightGen4416UnitsBridge `
           LRATCatcher.Tests.R45DegreeEightLeafAssemblyCore `
           LRATCatcher.Tests.R45DegreeEightPilot `
           LRATCatcher.Tests.R45DegreeEightPilotSemantics `
           LRATCatcher.Tests.R45DegreeEightReducedAssignment `
           LRATCatcher.Tests.R45DegreeEightPilotAssembly `
           LRATCatcher.Tests.R45DegreeEightBranchComposition `
           LRATCatcher.Tests.R45DegreeEightGuardedMasterSemantics `
           LRATCatcher.Tests.R45DegreeEightGuardedMaster `
           LRATCatcher.Tests.R45RemainingDegrees
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

no_degreeEight_l22r01_of_catalogue_witnesses
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 8)
    (hred : CoveredByGen358Parent
      (redDegreeEightGraph coloring root hdegree)
      (gen358ParentIds.getD 22 0))
    (hblue : GraphIsomorphicFin
      (coloringGraph 16
        (blueDegreeSixteenColoring coloring root hroot hdegree))
      (gen4416Graph 1)) : False

no_root_has_redDegree_eight_certified
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring) :
    ∀ root, root < 25 →
      (colorNeighbors coloring root false).length ≠ 8

certified_exists_red_degree_ten_or_twelve
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring) :
    ∃ root, root < 25 ∧
      ((colorNeighbors coloring root false).length = 10 ∨
       (colorNeighbors coloring root false).length = 12)
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

The `R(4,5,25)` red-degree-eight split is closed and should not be redone:
the guarded master, all 54 admissible pair contradictions, the 59-cube cover
and the terminal rootwise theorem are compiled. The next formal objective is
to close the red-degree-10 and red-degree-12 cases. The checked global split
already reduces every hypothetical counterexample to one of exactly those two
degrees. The degree-eight construction is a reusable model for that work, not
the missing upper-bound theorem itself.

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
