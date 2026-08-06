# Next research checkpoint

## Proven and not to be redone

`R35CatalogCompleteness.lean` proves semantic completeness of every recorded
`R(3,5,n)` catalogue through order 14 using `GraphIsomorphicFin`.

The complete right-hand classification for the degree-eight `R(4,5,25)` split
is also closed. `R44Gen4416Classification.lean` proves:

```lean
ramseyFree_isomorphic_to_gen4416
    (coloring : Nat → Bool)
    (hfree : isRamseyFree 16 4 4 coloring) :
    ∃ targetIndex,
      targetIndex < gen4416GraphIds.length ∧
        GraphIsomorphicFin (coloringGraph 16 coloring)
          (gen4416Graph targetIndex)
```

This theorem already includes the rooted degree split, the `9 × 3` exhaustive
block catalogues, the semantics of the exact 10,880-clause CNF, its LRAT
replay, the 64 mask permutations and complementation. Do not rebuild an
`R(4,4,15)` catalogue or reopen the semantic right-cover obligation.

## Completed checkpoint — red-degree-eight branch

The complete red-degree-eight branch of the `R(4,5,25)` split is now closed
and should not be redone. The compiled chain contains:

- the exhaustive `gen358` and `gen4416` catalogue covers;
- the block-preserving ambient permutation and literal-level unit bridges;
- the generic 54-pair semantic assembly;
- `R45DegreeEightGuardedMasterSemantics`, which proves that UNSAT of the
  exact 282-variable, 55,926-clause guarded master implies
  `AllAdmissibleDegreeEightPairsContradictory`;
- `R45DegreeEightGuardedMaster`, which replays 59 trimmed leaf LRAT proofs
  plus the cover proof, checks exact CNF equality, and proves:

```lean
no_root_has_redDegree_eight_certified
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring) :
    ∀ root, root < 25 →
      (colorNeighbors coloring root false).length ≠ 8
```

The targeted terminal build completed 56/56 with no `sorryAx`. This is an
independent Lean/LRAT certification of one structural branch, not a proof of
`R(4,5) ≤ 25` and not a claim of new mathematics.

`R45RemainingDegrees` is also compiled. It combines the pre-existing checked
handshaking reduction to `{8, 10, 12}` with the new exclusion and proves
`certified_exists_red_degree_ten_or_twelve`: every hypothetical counterexample
has a red-degree-10 or red-degree-12 root.

The 59 leaf proofs total about 2.4 GB and currently live outside Git behind the
ignored `guarded_master/proofs/` junction. The generated `metadata.json` is a
frozen pre-solver metadata snapshot; its proof-artifact inventory records the
state before the full certificate run and is not a post-run completeness
claim. `proof_bundle_manifest.json` is the post-certification manifest: it
records the 59 leaf LRAT files, the cover LRAT file, their hashes and the
successful Lean replay. A portable release must provide the external bundle
matching that manifest and automate its retrieval and verification.

## Immediate target — remaining `R(4,5,25)` root degrees

Use the degree-eight guarded-master architecture as a template for exactly the
red-degree-10 and red-degree-12 branches. The checked global dispatch to those
two cases is already proved in `R45RemainingDegrees`: these are exactly the
remaining red-root-degree cases. Do not reopen the earlier `7..13` window or
rebuild a broader degree split. Do not reopen the degree-eight local
catalogues, its 54 pair contradictions, or its terminal composition.

Closing these remaining degree branches would establish `R(4,5) ≤ 25`.
Until that composition exists, the degree-eight theorem is only one completed
case of the upper-bound proof.

## Subsequent global target — `R(5,5)`

Prove a Lean coverage theorem of the following shape:

```lean
theorem every_r55_free_k43_enters_tight_manifest :
  IsR55Free graph → graph.order = 43 →
  ∃ branch ∈ tightManifest, BranchSemantics branch graph
```

The shortest route currently appears to be:

1. formalize the minimum-degree anchor and its complement symmetry;
2. **partially done:** `R55DegreeBounds.lean` derives red and blue degree at
   most 24 from `R(4,5) ≤ 25`; produce that remaining upper-bound certificate
   using canonical root degrees and a checked symmetry/cube cover;
3. **done for exact `d=20,c=10`:** use
   `r35_catalogue_order_ten_complete` for the common-neighbour type, via
   `d20c10_type_covered_by_orderTenCatalogue`;
4. prove the rooted cardinality counters and regularity clauses sound;
5. prove signature-lex constraints choose an orbit representative without
   removing all labelings;
6. connect each manifest leaf to its exact CNF assumptions and LRAT theorem.

The 313 `d=20,c=10` cases are already solver-UNSAT, but only two leaves have
formal LRAT imports. Do not promote solver results to a global theorem without
the coverage and composition steps above.

The naive `R(4,5,25)` CNF is not a viable monolithic LRAT target: it remains
`UNKNOWN` after five million conflicts, and one million conflicts already
generate 448 MB of incomplete textual proof. See
`RAMSEY_BOUND_DIAGNOSTICS.md`. The finite split fixes a root, uses
`R(3,5) ≤ 14` and the now-certified `R(4,4) ≤ 18` to restrict its red degree
to `7..13`; parity then selects an even red degree in `{8, 10, 12}`. For
degree 8, both local catalogue covers, the generic unit/permutation assembly,
the guarded master and all 54 pair contradictions are now certified.
`no_root_has_redDegree_eight_certified` closes that branch unconditionally,
and `R45RemainingDegrees` leaves exactly the red-degree-10 and red-degree-12
branches and their checked composition.

The canonical local constructor is now complete. `LocalD20C10Witness` asks
only for `degree(root)=20`, `anchor ∈ N(root)` and
`codegree(root,anchor)=10`; `LocalD20C10Witness.package` builds the exact
lists and induced graph, and
`LocalD20C10Witness.covered_by_orderTenCatalogue` proves catalogue coverage.

For this separate `K43` line, the next Lean lemma is the global/branch
reduction producing such a witness from `isRamseyFree 43 5 5` plus the
selected `d=20,c=10` branch. After that, identify the representative index and
connect it to the manifest/CNF branch semantics.

For the canonically labelled branch,
`LocalD20C10Witness.ofCanonicalBranch` and
`canonicalBranch_covered_by_orderTenCatalogue` are complete. The next exact
interface was also completed in `R55CanonicalUnitsBridge.lean`: satisfaction
of the 42+19 DIMACS units yields both canonical list equalities, a local
witness and catalogue coverage. The one-based DIMACS / zero-based Lean shift
is explicit and independently audited.

`R55CanonicalCommonIndex.lean` now proves
`common units.toLocalWitness.toExactLists i = i.val + 2` and identifies every
bit of the induced graph with its ambient edge on vertices `2,…,11`. The next
typed-branch bridge is now complete in `R55TypedUnitsBridge.lean`: all 45
literals emitted by `fixed_anchor_type_clauses` are characterized, and their
satisfaction is equivalent to literal packed-graph equality with the chosen
Lean catalogue entry. Index 312 is proved to equal W5.

The remaining external-index obligation is to certify that graph6 record `i`
and manifest `type_index=i` denote `orderTenCatalogueType i`, and that the CNF
contains the corresponding 45 units. In parallel, the WLOG/relabeling theorem
must derive the canonical units from an arbitrary relevant `K43` branch.

`R55ColoringPermutation.lean` now proves the full equivalence
`isRamseyFree 43 5 5 coloring ↔ isRamseyFree 43 5 5 (permuteColoring p coloring)`
for every finite vertex permutation. The remaining WLOG task is to instantiate
such a permutation from the exact degree-20/codegree-10 witness and prove that
the resulting coloring satisfies the canonical units.

That instantiation is now complete in `R55CanonicalRelabeling.lean`.
`LocalD20C10Witness.canonical_ramseyFree_and_units` constructs a genuine
permutation of all 43 vertices, preserves Ramsey-freeness, and proves the 61
canonical root/anchor units. The remaining global-coverage task is to derive
the appropriate local witness (or the alternative degree/codegree branches)
from an arbitrary hypothetical `K43` Ramsey-free coloring.

The certified type-0 leaf is now decomposed exactly by
`R55MinLeafBridge.lean` and `R55MinLeafSemantics.lean`. The terminal theorem
derives contradiction from Ramsey-freeness, canonical/type-0 units, and the
explicit hypothesis `CounterBlocksSatisfied`. Consequently the semantic
residue for this leaf is no longer vague: prove soundness and witness
extension for exactly the rooted-degree counter block (116,928 clauses) and
minimum-internal-degree block (5,149 clauses).

## Verification and publication threshold

The targeted reproduction commands are:

```powershell
python -m unittest scripts.r45_d8_pilot.test_gen4416_rooted_classifier `
  scripts.r45_d8_pilot.test_gen4416_rooted_proof_artifacts
python scripts\r45_d8_pilot\gen4416_rooted_classifier.py verify

cd vendor\lrat-catcher
lake build LRATCatcher.Tests.R44Gen4416TargetAudit `
  LRATCatcher.Tests.R44Gen4416Classification `
  LRATCatcher.Tests.R45DegreeEightGen4416Bridge `
  LRATCatcher.Tests.R45DegreeEightGlobalPermutation `
  LRATCatcher.Tests.R45DegreeEightRawGen4416Bridge `
  LRATCatcher.Tests.R45DegreeEightGen358UnitsBridge `
  LRATCatcher.Tests.R45DegreeEightGen4416UnitsBridge `
  LRATCatcher.Tests.R45DegreeEightLeafAssemblyCore `
  LRATCatcher.Tests.R45DegreeEightReducedAssignment `
  LRATCatcher.Tests.R45DegreeEightPilotAssembly `
  LRATCatcher.Tests.R45DegreeEightBranchComposition `
  LRATCatcher.Tests.R45DegreeEightGuardedMasterSemantics `
  LRATCatcher.Tests.R45DegreeEightGuardedMaster
```

The literature audit rules out claims of a first classification, a first
formalization or a new mathematical result. McKay's
[Ramsey graph catalogue](https://users.cecs.anu.edu.au/~bdm/data/ramsey.html)
already lists two `R(4,4,16)` graphs, while Gauthier–Brown's
[*A Formal Proof of R(4,5)=25*](https://arxiv.org/abs/2404.01761) formalizes
the relevant enumeration and coverage in HOL4. Describe this checkpoint as an
independent Lean/LRAT certification. Publication is plausible only if its
architecture, compositional proof design or certificate methodology is
sufficiently distinct from that prior work.

Do not describe it as a new Ramsey bound or as evidence that `R(5,5)=43`. Its
explicit trust boundary is the Lean kernel, standard classical/quotient
axioms, and the native LRAT/`native_decide` bridges used for the finite
certificates; there is no `sorryAx`.
