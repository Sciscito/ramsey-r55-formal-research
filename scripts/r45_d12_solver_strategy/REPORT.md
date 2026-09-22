# d12 solver strategy: measured status and next certificate architecture

Date: 2026-08-07

## Result status

There is no new proof of `R(4,5) = 25` and no major publishable mathematical
breakthrough in this work yet.  The useful result is narrower and fully
reproducible: a one-row monotone constraint in every one of the twelve `d12`
cases has been compressed into a small exact disjoint cube cover.  This gives
a plausible certificate architecture, but a bounded solver probe shows that
this one-row split alone is not sufficient.

All large catalogues, generated CNFs, and solver outputs are on `S:`.  This
directory contains only small source and test files.

## Exact one-row cover

Fix one of the twelve `R(3,5,12)` graphs `A`.  If a new `B` vertex is blue to
the deleted root, its red-neighbour mask in `A` must meet every independent
4-set of `A`.  `cross_interval_cover.py` solves this 12-variable monotone
Boolean problem exactly by dynamic programming over at most `3^12` partial
assignments.  It emits a disjoint accepted cube cover and audits all 4096 total
assignments.

| `A` catalogue index | admissible masks | automorphism orbits | exact cubes |
|---:|---:|---:|---:|
| 0 | 2187 | 1113 | 81 |
| 1 | 2221 | 607 | 75 |
| 2 | 2098 | 534 | 76 |
| 3 | 2116 | 1091 | 76 |
| 4 | 2013 | 1019 | 77 |
| 5 | 2101 | 565 | 85 |
| 6 | 2013 | 599 | 76 |
| 7 | 2102 | 557 | 78 |
| 8 | 2102 | 197 | 79 |
| 9 | 1926 | 270 | 80 |
| 10 | 2342 | 87 | 82 |
| 11 | 2273 | 319 | 88 |
| **total** | **25,494** | **6,958** | **953** |

The accepted cubes assign between 4 and 12 literals.  For an unconditional
iCNF-style cover, the rejected region must also be covered; the direct
monotonicity witnesses are the 18--34 independent 4-sets of `A` (23 for type
0).  Overlap among rejected cubes is harmless for a cover proof but must be
handled explicitly if an exact partition is required.

## Bounded solver evidence

The baseline CNF `leaf_01.cnf` has 276 variables and 53,911 clauses.  Its
SHA-256 is
`3C01B8B4B863174D655804B7DAE162D51166E4142D07101CDE4925246D71A54E`.

| experiment | result | cost / observation |
|---|---|---|
| monolithic, 1M conflicts | `UNKNOWN` | about 31--35 s |
| monolithic, 5M conflicts | `UNKNOWN` | 256.5 s |
| global degree bounds, 1M | `UNKNOWN` | about 45 s |
| cross-row lex ordering, 1M | `UNKNOWN` | 41.8 s; slower |
| one rooted `R(4,4,12)` case, 1M | `UNKNOWN` | 49.0 s; slower |
| naive four-literal split, 16 cubes | 1 `UNSAT`, 15 `UNKNOWN` | 3.0M conflicts, 25.5 s; the sole UNSAT cube is trivial |
| exact type-0 interval split, 81 cubes | 0 `UNSAT`, 81 `UNKNOWN` | 50k conflicts/cube, 4,050,077 total, 33.249 s wall |

For the 81-cube run, individual solver times were 1.39--1.77 s (median
1.55 s), with no timeout and no SAT result.  The generated 82 files occupy
158,023,370 bytes, entirely under:

`S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-solver-strategy\interval_t00_b12_c50k`

The JSON explicitly labels this run `PROOF_FREE_SEARCH_PROBE_ONLY`; it is not
a certificate.

## Published facts versus present contribution

McKay and Radziszowski already proved `R(4,5) = 25` and reported the key
feasible-cone/interval strategy in 1995.  In particular, their fifth-row
calculation used a covering family of 74 graphs (23 of order 7 and 51 of order
8), rather than branching over all 1,449,166 graphs in `R(4,4,12)`.  Therefore
the mathematical idea of interval or feasible-cone decomposition is
published and must not be claimed as new.

References:

- Brendan McKay and Stanislaw Radziszowski, *R(4,5)=25*, Journal of Graph
  Theory 19 (1995): <https://users.cecs.anu.edu.au/~bdm/papers/r45.pdf>
- Official Ramsey graph data: <https://users.cecs.anu.edu.au/~bdm/data/ramsey.html>

Official data mirrored on `S:` and checked locally:

| file | records | SHA-256 |
|---|---:|---|
| `r44_7.g6` | 362 | `6A3DA7F0687C392420F190DB0643B5C5B7ECB1A3C5ED098C7D96200185A5F010` |
| `r44_8.g6` | 2079 | `B27389F7B1C70F823161A2CCA629BED3F4FBF058A43907637C0F9CE2E0CC4AB3` |
| `r44_12.g6.gz` | 1,449,166 after decompression | `4CC7E477D544808D260C61422FE7017DD57D683AC7CC56262DBE991F8463E18F` |
| `r44_12.g6` | 1,449,166 | `C6A60EE177E00C1168259A5BD464F9CFA5A5B471AE2BA1811E7B3FAF23144E7A` |

The exact 953-cube computation and its LRAT-oriented implementation are an
independent engineering result here.  Their novelty in the research
literature has not been established.  A potentially publishable contribution
would be a small, independently checkable modern certificate stack (including
coverage and composition), not a claim to have rediscovered the 1995 theorem.

## Recommended next step

1. Reconstruct a small order-7/order-8 covering family from the official
   catalogues and verify, against all 1,449,166 order-12 records, that every
   record contains a selected member.  Emit machine-checkable witnesses and
   hashes.  The paper's exact 74 selected records are not present in the data
   page, and selecting merely the densest graphs is not justified because of
   density ties.
2. Combine that structural cover with the exact cross-row cubes.  Benchmark a
   small stratified sample before generating any full proof batch.
3. Only after the sample exhibits decisive UNSAT rates, generate CaDiCaL LRAT
   leaves on `S:` and compose: coverage certificate + cube cover certificate +
   leaf LRAT certificates + Lean checker theorem.
4. Compare the reconstructed cover/certificate size with the 1995 family.  A
   strictly smaller verified cover or a substantially simpler formal proof
   architecture would be a meaningful research target; neither has been
   achieved yet.

## Reproduction

From this directory, using the repository's Python environment:

```powershell
python -m unittest -v test_solver_strategy.py
python cross_interval_cover.py
python interval_benchmark.py `
  --input S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-probe\leaf_01.cnf `
  --solver S:\CodexResearchCache\ramsey-formal\lean-toolchains\leanprover--lean4---v4.30.0\bin\cadical.exe `
  --output S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-solver-strategy\interval_t00_b12_c50k `
  --catalogue-index 0 --b-vertex 12 --conflicts 50000 --timeout 30 --jobs 4
```

The benchmark refuses to overwrite an existing `results.json`, so use a new
output directory for a fresh run.
