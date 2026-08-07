# Degree-12 conditioned-cover prototype

Status: one nontrivial conditioned cube for `A` catalogue type 0 is now
UNSAT with an LRAT replayed by Lean. This is a verified local lemma, not a
complete cover of the degree-12 branch.

## Exact result

The direct `A=type0` leaf has 276 variables, 53,911 clauses, and SHA-256
`3C01B8B4B863174D655804B7DAE162D51166E4142D07101CDE4925246D71A54E`.
It remained `UNKNOWN` after 1,000,000 conflicts without conditioning.

The complemented image of official `gen4412` parent 1 fixes 58 of the 66
edges in `B`. Its conditioned leaf is UNSAT in 74,362 conflicts. Backward
dependency tracing of its LRAT reduced it to 53 units. A deterministic
ascending greedy deletion pass, with a limit of 200,000 conflicts per
deletion, then found this 24-unit cube:

```text
229 231 -234 238 -239 243 247 248 251 -252 253 254
255 -256 -258 259 260 261 262 265 266 268 274 275 0
```

The other 42 `B` edges are holes. The resulting formula has 53,935 clauses:

- CNF SHA-256: `68B13279F9AF788BA9963EF9B2AC5CCFD94994A4853856F4F8E903153B35B91E`
- CaDiCaL result: UNSAT, 194,810 conflicts, 5.92 solver seconds
- LRAT bytes: 39,197,795
- LRAT SHA-256: `A543FFE21C7AE848DF977D1472A414BBD3F3DE5545698AC6417542BCC3376D39`
- Lean replay: success in 9.387 seconds
- Lean trim: 253,681 to 229,366 actions; 39,197,795 to 29,514,347 UTF-8 bytes
- replay theorem: `LRATCatcher.Tests.R45D12ConditionedCoreReplay.d12_type0_core24_unsat`

The replay uses the expected native checker axiom plus `propext`,
`Classical.choice`, and `Quot.sound`.

A reverse-order greedy pass found a different 26-unit DIMACS cube, with 12
literals shared with core 24 and no opposite literal. It re-solves UNSAT in
187,483 conflicts and has CNF SHA-256
`8E417B1F45DE1256AEE69236BD8826DEA5AA9B8A6876A4FEB80A1EC36EA25505`.
It is a proof-free secondary discovery until its own LRAT is generated and
replayed.

## Convention audit

`gen4412` is decoded with the `graph.sml` upper-triangle ternary order. The
raw HOL convention is colour 1 = blue = negative DIMACS and colour 2 = red =
positive DIMACS. The artifacts in this report deliberately use the opposite,
complemented orientation: HOL 1 maps to positive and HOL 2 to negative.
Colour 0 is a hole. Local `B` vertex `i` maps to global non-root vertex
`12+i`; consequently the 66 `B-B` variables are exactly 211 through 276.

Before using a parent, the probe checks every listed child against the stored
normalisation permutation with the independent official-cover checker. The
inverted physical polarity also appears in the degree-eight direct pipeline,
where the whole HOL formula is clause-wise complemented. Here there are two
legitimate routes to composition: prove a direct `R(4,4)` catalogue theorem
that treats encoded colour 1 simply as graph adjacency, or transport an
explicit complement from the physical HOL colour names. The `R(4,4)`
condition is self-complementary, but one of these bridges must be formalised.
The current LRAT proves the exact DIMACS cube independently of this catalogue
interpretation.

The CLI now requires `--orientation raw` or `--orientation complemented` for
every operation that interprets HOL colours. This prevents either convention
from being selected silently.

## Raw-orientation control

As a polarity control, physical-HOL parent 1 was also tested with colour 1 as
negative DIMACS and colour 2 as positive DIMACS. It remained `UNKNOWN` after
1,000,004 conflicts and 59.669 wall seconds:

- raw-parent CNF SHA-256: `7630F4428F77E2CCC336DB3F06EEBCAC20D09F86E1D16C761B498A3B0639F965`
- solver-log SHA-256: `B2A7C6CF623477C89851302572C2E93D10ABFEAEACF57A090C17A87F9EF73427`

This does not establish satisfiability or impossibility in the raw
orientation. It shows that the catalogue-adjacency/inverted-label route is a
material search advantage rather than a cosmetic renaming.

## Measured scope

The 24-unit cube is directly implied by only the complemented image of parent
1 among all 26,845 `gen4412` parents. It is broader modulo relabelling of `B`.

A deterministic Algorithm-R reservoir sample without replacement used seed
`20260807` and selected 1,000 of the 1,449,166 official child instances.
For every selected encoded graph, an exact backtracking search checked all
possible 12-vertex bijections with colour 1 interpreted as adjacency. Relative
to the physical HOL colour names this is the complemented orientation; as an
uncoloured graph catalogue it is a direct adjacency interpretation. Fourteen
graphs matched the cube under some permutation: 1.4%. The descriptive 95%
Wilson interval is 0.8358% to 2.3362%, corresponding to
about 20,288 catalogue classes with an interval of roughly 12,111 to 33,856.

This interval measures sampling uncertainty only. It is not a formal bound,
and it relies on the separately audited official child list as the target
population. The report stores the seed and all selected global indices, so
the sample is exactly reproducible.

## What remains

This result does not close `A=type0`, let alone the full degree-12 branch.
The next proof obligations are:

1. discover enough conditioned cubes to cover every admissible `B` graph
   modulo permutation and the explicitly selected raw/complemented orientation;
2. certify that cover, rather than infer it from sampling;
3. bridge the selected catalogue interpretation, the cube units, and the
   required `B` relabellings into Lean;
4. repeat or generalise the construction across all twelve `A` types;
5. compose those branches with the existing selector theorem.

The local result is useful because it changes the granularity: under the
catalogue-adjacency / inverted-physical-label interpretation, one 24-edge
partial motif appears to cover on the order of tens of thousands of official
classes, whereas one
`gen4412` parent lists at most 256 children. That compression is an
experimental signal, not yet a publishable global theorem.

## Disk policy and artifacts

All CNFs, solver logs, LRAT files, samples, and replay outputs are under:

```text
S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-conditioned-cover
```

Only this small probe, its tests, and this report live in the repository.
The Python test suite currently contains ten deterministic tests, including
the ternary-to-DIMACS mapping, LRAT backward dependency extraction, stored
permutation orientation, explicit raw/complemented polarity, exact
permutation matching, and Wilson interval.