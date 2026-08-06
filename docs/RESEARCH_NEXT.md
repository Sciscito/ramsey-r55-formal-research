# Next research checkpoint

## Proven and not to be redone

`R35CatalogCompleteness.lean` proves semantic completeness of every recorded
`R(3,5,n)` catalogue through order 10 using `GraphIsomorphicFin`.

## Immediate target

Prove a Lean coverage theorem of the following shape:

```lean
theorem every_r55_free_k43_enters_tight_manifest :
  IsR55Free graph → graph.order = 43 →
  ∃ branch ∈ tightManifest, BranchSemantics branch graph
```

The shortest route currently appears to be:

1. formalize the minimum-degree anchor and its complement symmetry;
2. derive the neighbourhood/non-neighbourhood `R(3,5)` and `R(4,5)` local
   predicates;
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

The canonical local constructor is now complete. `LocalD20C10Witness` asks
only for `degree(root)=20`, `anchor ∈ N(root)` and
`codegree(root,anchor)=10`; `LocalD20C10Witness.package` builds the exact
lists and induced graph, and
`LocalD20C10Witness.covered_by_orderTenCatalogue` proves catalogue coverage.

The immediate Lean lemma is therefore the global/branch reduction producing
such a witness from `isRamseyFree 43 5 5` plus the selected `d=20,c=10`
branch. After that, identify the representative index and connect it to the
manifest/CNF branch semantics.

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
In parallel, the WLOG/relabeling theorem must derive the 61 canonical units
from an arbitrary relevant `K43` branch.
