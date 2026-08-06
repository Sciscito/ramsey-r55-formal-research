# Next research checkpoint

## Proven and not to be redone

`R35CatalogCompleteness.lean` proves semantic completeness of every recorded
`R(3,5,n)` catalogue through order 10 using `GraphIsomorphicFin`.

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

## Immediate target — lift the degree-eight witnesses into `K25`

The existential local composition is now complete. The compiled theorem
`degree_eight_enters_gen358_and_gen4416` composes
`degree_eight_local_split`, `every_r35_order_eight_graph_enters_gen358` and
`ramseyFree_isomorphic_to_gen4416`: every `(4,5)`-free `K25` branch with a red
degree-eight root simultaneously enters a certified `gen358` parent on the
red block and a certified `gen4416` target on the complemented blue block.
The module `R45DegreeEightGen4416Bridge.lean` has SHA-256
`85B0DBF179D2DA759AA14D13E0834D788255E0B0F33003BDDD5937ABA4B031B5`.

The next gap starts strictly after this existential conjunction:

1. lift the two local isomorphisms to one block-preserving permutation of all
   25 vertices, fixing the root;
2. prove that this permutation satisfies the exact `gen358` and `gen4416`
   parent-unit clauses, with the raw/complemented color convention explicit;
3. generate and replay the 53 LRAT certificates still missing;
4. compose the 54 leaf contradictions with the parent coverage to obtain a
   Lean theorem excluding red root degree 8 in a `(4,5)`-free `K25`.

This would be a certified structural case toward `R(4,5) ≤ 25`, not yet the
full upper bound. The other root-degree branches and their checked coverage
would still remain.

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
to `7..13`, canonically relabels the two neighbourhoods, and certifies those
seven branches plus the relabeling/coverage theorem. For degree 8, both local
catalogue covers are now formal; the remaining gap starts at their simultaneous
lift to `K25` and the exact leaf units.

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
  LRATCatcher.Tests.R45DegreeEightGen4416Bridge
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
