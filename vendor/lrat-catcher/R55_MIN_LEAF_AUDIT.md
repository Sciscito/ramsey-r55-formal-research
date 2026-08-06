# Audit of the certified `d20_c10_t0` minimum-anchor leaf

This note records exactly what is certified and what is still assumed by the
semantic bridge. It must not be read as a proof of the full `R(5,5) <= 43`
claim.

## Checked artifacts

- `r55/min_d20_c10.cnf`
  - SHA-256: `F801B48C62AB54A8587558E169BB8FA4CEC0E43C39EE1D9911088CCAD36A32AC`
  - DIMACS header: `p cnf 62184 2047379`
- `r55/min_d20_c10_t0.lrat`
  - SHA-256: `BE15256C842DF64E9D0301CA5398F2C4E03C530A391840410631B830F97DC44C`
  - size: 29,293,939 bytes
- `r55/r35_10.g6`
  - SHA-256: `194D2F95511F562E44A4137B1B91633F182E2ADB14E7EA6880FA1B052BCBB3BB`

`R55MinLeafBridge.lean` replays the LRAT certificate and gives the parsed CNF
a reusable name. `R55MinLeafSemantics.lean` checks the complete decomposition
below with `native_decide` and proves the conditional semantic contradiction.

## Building from a source-only checkout

The 90 MB CNF and 29 MB LRAT proof are intentionally not stored in Git. They
are release artifacts. Download and extract the private repository release so
that these paths exist before building the two leaf modules:

- `r55/min_d20_c10.cnf`
- `r55/min_d20_c10_t0.lrat`

The default lightweight source smoke test deliberately excludes
`R55MinLeafBridge` and `R55MinLeafSemantics`; including them without the
release artifacts would fail for a missing file rather than for a proof
error. With the artifacts restored, run:

```powershell
lake build LRATCatcher.Tests.R55MinLeafSemantics
```

## Exact clause layout

All intervals below are zero-based and half-open.

| Interval | Count | Meaning |
|---|---:|---|
| `[0, 1925196)` | 1,925,196 | two Ramsey clauses for every 5-subset of 43 vertices |
| `[1925196, 2042124)` | 116,928 | rooted red/blue degree-window sequential counters |
| `[2042124, 2047273)` | 5,149 | anchored minimum internal-red-degree counters |
| `[2047273, 2047315)` | 42 | `N_R(0) = {1,...,20}` units |
| `[2047315, 2047334)` | 19 | common red neighbours of `(0,1)` are `{2,...,11}` |
| `[2047334, 2047379)` | 45 | all edges/non-edges of catalogue type index `0` |

The edge variables are DIMACS variables `1..903`. The rooted counter uses
auxiliaries `904..59619`; the minimum-internal-degree counter then uses
`59620..62184`.

The final 45 literals are checked against Lean's generated order-ten
catalogue representative at zero-based index `0`; this catches both graph6
ordering and DIMACS/Lean indexing mistakes.

## Published Lean statements

- `minD20C10T0Formula_unsat`: the exact parsed external formula is UNSAT.
- `minD20C10T0Formula_eq_decomposition`: the complete parsed formula equals
  the six-block Lean decomposition above.
- `pythonInterleavedRamseyEncode_sat`: Ramsey-freeness satisfies the exact
  Python ordering of the Ramsey prefix.
- `unitsCNF_sat_iff`: unit-list semantics agrees exactly with the corresponding
  CNF block.
- `no_t0_assignment`: contradiction from Ramsey-freeness, the canonical
  root/anchor units, the type-0 units, and explicit satisfaction of both
  auxiliary counter blocks.

The two principal theorems compile without `sorry`, `admit`, `unsafe`, or a
new explicit axiom. Their printed axiom sets contain the expected standard
quotient/classical axioms and the named `native_decide` certificate axioms.

## Obligations deliberately not hidden

`no_t0_assignment` takes `CounterBlocksSatisfied assignment` as an explicit
hypothesis. The following implications are not yet claimed:

1. a Ramsey-free coloring has the global degree window encoded by the rooted
   counter (this requires a formal `R(4,5) = 25` consequence);
2. each mathematical at-most bound admits auxiliary bits satisfying the exact
   sequential-counter clauses;
3. the anchor can be chosen and relabelled as a minimum-red-degree vertex of
   the root neighbourhood, justifying internal red degree at least ten for
   every other root neighbour;
4. an isomorphism to catalogue type `0` can be transported to the exact
   labelled type units when this branch is selected.

Until these are discharged, the LRAT leaf eliminates precisely the fully
labelled, counter-satisfying type-0 branch—not every abstract coloring in the
`d=20,c=10` stratum.
