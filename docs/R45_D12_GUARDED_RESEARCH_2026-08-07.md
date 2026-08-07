# Degree-12 guarded research checkpoint

Date: 2026-08-07

## Scientific outcome

This checkpoint does not prove `R(4,5) <= 25` and does not improve a Ramsey
number. The degree-eight branch is certified, while the degree-ten and
degree-twelve branches remain. For degree twelve, **0 of the 12 mathematical
left-catalogue cases are completely closed**.

### Later structural addendum

The guarded-gluing measurements below remain valid historical experiments,
but two later results supersede their structural-cover status. First, all 13
exact degree-eight residual CNFs of the catalogue-independent `cover9`
target now have LRAT refutations replayed by Lean, and Lean separately proves
the exact two-centre normalization and 13-case disjunction. The CNF semantic
bridge and composition remain open. Second, the exact complement-closed
order-seven minimum is now six classes (three complement pairs), not the
earlier eight-class closure candidate. Its upper bound covers all 1,449,166
frozen catalogue records; its lower bound excludes one or two pairs on 30
explicit valid graphs. See
`scripts/r45_d12_complement_closed_minimum/MANIFEST.json` and
`docs/NEXT_CONVERSATION_HANDOFF_2026-08-07.md`.

These advances do not change the guarded-gluing counter: it remains **0/12**.

What is now verified is the certificate architecture through a
catalogue-relative right-block cover: the semantic split, selector encoding,
global permutation, exact left-catalogue units, a polarity-explicit generic
partial-pattern bridge, several exact local LRAT refutations, and a minimal
five-motif order-seven cover of every record in the frozen `r44_12.g6`
catalogue. The missing theorem is a refutation, or a checked cover by
tractable UNSAT leaves, for every resulting gluing leaf and every one of the
twelve left types. A portable catalogue-independent upper theorem would be a
separate strengthening.

## Verified semantic layer

The Lean modules establish the following chain without `sorry` or `admit`:

1. an exact red degree of twelve partitions the non-root vertices into two
   blocks of size twelve;
2. the red-neighbour block is one of the twelve exhaustive
   `R(3,5,12)` catalogue types;
3. a genuine permutation of `Fin 25` fixes the root and independently
   relabels the two blocks;
4. the selected left type implies the exact 66 DIMACS units on variables
   `1..66`;
5. a generic partial right-block pattern emits units only on variables
   `211..276` and has literal-level semantics for both named colour
   orientations.

The strongest current entry theorem is
`red_degree_twelve_enters_encoded_catalogue_unit_case`. It reaches a real
catalogue case and its selector/left units, but it does not yet prove the
53,845 base clauses or select a complete right-cover leaf.

## Frozen guarded formula

The solver-free generator constructs:

- 276 non-root edge variables and four selector variables;
- 53,845 fixed-root base clauses;
- 792 guarded left-catalogue units;
- one blocker for selector codes 12 through 15;
- 280 variables and 54,638 clauses in total;
- 13 cover cubes: twelve valid full selector codes and one partial invalid
  code cube.

Important hashes:

- guarded master CNF:
  `0F5049E4D2A7B465E33BA852170477711CA63220ED6F2DAD1542C558D4D8BFA8`;
- order-12 left catalogue:
  `322E7A54E67F4201BD37998AB420AFB3EEE41B1DCD6B277B7F055BDA152DA95E`.

The invalid-selector leaf has a checked LRAT. This closes only an
administrative encoding case; all twelve mathematical leaves remain open.

## Exact local LRAT results

Two nontrivial right-block conditionings have independently replayed in
Lean against their exact CNFs.

### Two-centre motif 64

- 59 fixed right-block units;
- left catalogue type 1;
- UNSAT after 305,787 CaDiCaL conflicts;
- CNF SHA-256:
  `2A82407F384C3DA3661651738A0D6884844753353BBA7AC4B56CF6FF2E00BD9F`;
- LRAT size: 62,911,549 bytes;
- LRAT SHA-256:
  `4556AE3A2BDFFD54FC15BEAB21AD86BD8B475063CE54A75A34BECE22B42F072D`.

### Conditioned core 24

- 24 fixed right-block units and 42 holes;
- left catalogue type 0;
- UNSAT after 194,810 conflicts;
- CNF SHA-256:
  `68B13279F9AF788BA9963EF9B2AC5CCFD94994A4853856F4F8E903153B35B91E`;
- LRAT size: 39,197,795 bytes;
- LRAT SHA-256:
  `A543FFE21C7AE848DF977D1472A414BBD3F3DE5545698AC6417542BCC3376D39`.

A reverse greedy deletion order found a different 26-unit UNSAT cube at the
solver level. It is deliberately labelled proof-free until a separate LRAT
is generated and replayed.

These are valid local lemmas. Neither one implies a complete degree-twelve
case without a checked coverage theorem.

## Cover experiments

### Five-motif order-seven cover and minimum

The five graph6 motifs

- `F@h^g`;
- `FCUrO`;
- `FDLmW`;
- ``FG`Xo``;
- `FdW}w`

cover all 1,449,166 records in the frozen order-12 source. This upper result
is explicitly **relative to that catalogue**: the source `r44_12.g6` has
SHA-256
`C6A60EE177E00C1168259A5BD464F9CFA5A5B471AE2BA1811E7B3FAF23144E7A`,
the five-row cover has SHA-256
`CEAE61F737722C6D1392B5C8D654FC1B09D482AA3C76222EE2D9CBFF3CA5E288`,
the compact incidence certificate has SHA-256
`38E61DABA2597AAADC0821F6738059091FAAAFF7F97968D094EDA17826A8510E`,
and the independently replayed 1,449,166-entry induced witness has SHA-256
`36EC5E95D8599F6AE8099A6D3376D0E3F43269059FC644A1A3F96C52846414CB`.

Minimality among order-seven motifs has a separate lower-bound certificate.
It uses an explicit 25-graph `R(4,4,12)` kernel and does not assume
completeness of the order-12 catalogue. Exhaustive enumeration checks all
`2^21` labelled order-seven graphs: exactly 923,012 are `R(4,4)`-free, and
they coincide with the permutation closure of the 362 official order-seven
classes. The source order-seven catalogue has SHA-256
`6A3DA7F0687C392420F190DB0643B5C5B7ECB1A3C5ED098C7D96200185A5F010`.
The kernel report has SHA-256
`46BA1FEA2EB4415DD96C602074AD393B471876ED2FA7A1DBE4AE5EC24A19785D`,
the 49,015-byte no-cover-four CNF has SHA-256
`84E1BE500A85AD2B6F63F780063116F4AF0DE3239C63710AFF8816057AC6EF82`,
and its LRAT has SHA-256
`4FD1F02297F5019B9EADBE9BC20E29DF326B0B7F99B8A539C140FD9911F15793`.
The corrected exact Lean replay theorem is
`R45OrderSevenCoverMinimumReplay.no_order7_cover_of_size_four`; its replay
report has SHA-256
`DB075E5F11E664386B845131F1F6DECBFAB3B7832D107CA314029C773338A4F9`.

Therefore five is the exact minimum number of order-seven motifs covering
the frozen catalogue. No minimum is claimed for covers mixing order-seven
and order-eight motifs, and the result is neither a catalogue-independent
upper theorem nor a closure of any of the twelve degree-twelve cases.

### Catalogue-independent cover9 and complement-closed cover6 targets

The cover9 master still has no monolithic proof. It has 11,976,030 clauses
and SHA-256
`425676A0876F06BCE2D3477BB6D11A566D77C6DD7D7FD46E9A1B07D8E5C1C098`;
both it and the root-prefix variant timed out after 300 seconds without LRAT.

The degree-eight slice is no longer merely experimental. Its 13 exact
two-centre residual CNFs all have CaDiCaL LRAT refutations independently
replayed by LRAT-Catcher/Lean. The portable certificate manifest has SHA-256
`77FE47B5BC73865EDB0405DFC2D3B0A367C2A757B27A83CDC981D5958F80DE23`.
Lean separately proves the root permutation, degree bounds, second-centre
normalization, exact 13-case disjunction, and transport of `R(4,4)` freeness
and induced motifs. The missing obligation is the semantic CNF bridge and
composition with the 13 replays; other root degrees remain.

A later exact search also supersedes the eight-class complement prototype:
the complement-closed minimum is six order-seven classes, or three pairs, on
the frozen catalogue. The cover has zero holes, while a 30-graph explicit
kernel excludes one or two pairs. Its manifest is
`scripts/r45_d12_complement_closed_minimum/MANIFEST.json`. The associated
catalogue-independent cover6 reduction is exact on all 923,012 local
`R(4,4)` assignments. Its d8 formula is verified and seven of 13 residuals
are proof-free solver UNSAT; six residuals and all LRAT certificates remain.

Neither development closes a global degree-twelve gluing case.
### Two-centre consensus

A deterministic certificate transforms all 26,845 official `gen4412`
parents into 857 projected isomorphism classes and then 64 weak motifs. The
full coordinatewise consensuses contain 14 to 59 fixed literals. The
7,047,484-byte external certificate has SHA-256
`092EB9F45BD0F8761CF139677CBA3B11DB19575B6BFE103C7EB767AD5C388FDA`.

Regeneration checks all 26,845 parent assignments and their permutations.
Its mathematical scope is nevertheless conditional on the completeness of
the official 1,449,166-child `R(4,4,12)` source. Moreover, the dominant
14-unit motif and all 81 tested combinations with the one-row interval cover
remained `UNKNOWN` at their bounded conflict limits. Thus 64 is a cover-size
compression, not yet a solver breakthrough.

### A-dependent conditioned core

The core-24 motif was obtained from official parent 1 after LRAT dependency
extraction and bounded greedy deletion. An exact-permutation test on a
uniform reproducible sample of 1,000 official child instances found 14
matches. The descriptive rate is 1.4%, with a Wilson 95% interval of 0.8358%
to 2.3362%.

This is statistical evidence only. It neither proves a coverage fraction nor
establishes a full cover. Its possible value is architectural: conditioning
on the left type may yield much broader UNSAT motifs than an A-independent
right catalogue.

## Colour-orientation audit

The historical HOL archive calls colour 1 blue and colour 2 red. The fixed
root DIMACS assignment in this repository uses Boolean true/positive for the
opposite named Lean colour on the relevant transport. Both useful mappings
therefore exist and must never be implicit:

| Named orientation | HOL colour 1 | HOL colour 2 |
|---|---:|---:|
| `rawHOL` | DIMACS negative | DIMACS positive |
| `complementedB` | DIMACS positive | DIMACS negative |

The two-centre artifacts use `rawHOL`; the core-24 artifacts use
`complementedB`. Their exact CNF/LRAT claims are unaffected. A global theorem
must additionally provide the matching catalogue/complement transport before
using either coverage claim. The generic Lean bridge now encodes the
orientation as data and exports separately named end-to-end corollaries.

## Negative solver evidence

The following bounded attacks did not close a mathematical left type:

- direct type-0 leaf: `UNKNOWN` at 1M and 5M conflicts;
- global degree and lexicographic variants: `UNKNOWN` and slower;
- rooted `R(3,4)` split: `UNKNOWN` and slower;
- exact 81-cube one-row split: 81/81 `UNKNOWN` at 50k conflicts;
- dominant two-centre motif combined with those 81 cubes: 81/81 `UNKNOWN`
  at 200k conflicts, 16,200,094 conflicts total;
- all five catalogue-relative cover motifs on left type 0: 5/5 `UNKNOWN` at
  both 100k and 200k conflicts.

These measurements rule out several tempting but weak decompositions. The
minimal order-seven cover now supplies the structural layer; the active task is
to find and certify gluing-aware, A-dependent UNSAT leaves for its motifs, while
the catalogue-independent target remains a separate proof obligation.

## Historical baseline and novelty threshold

McKay and Radziszowski reported in 1995 that their degree-twelve calculation
used 23 `R(4,4,7)` graphs and 51 `R(4,4,8)` graphs to cover all
`R(4,4,12)` graphs, but did not publish the 74-record list. Gauthier and Brown
later formalized `R(4,5)=25` in HOL4; their exact order-12 cover has 26,845
generalizations and their degree-twelve computation comprises 12 gluing
theorems.

Consequently, rediscovering that `R(4,5)=25` or using generic interval search
is not novel. A credible publication target here would require at least one
of:

- a new, independently checkable structural cover, preferably smaller than
  74 or materially easier to certify;
- a much smaller A-dependent conditioned cover with full exact witnesses;
- a reusable Lean/LRAT cube-and-cover architecture whose proof objects are
  substantially smaller and independently replayable;
- completion of degree twelve and degree ten into a second formal proof with
  a clearly different trusted base and certificate method.

The five-motif result reaches the threshold of a credible structural
candidate, but its novelty priority is not yet established. Publication is
credible/potential only after a broader bibliographic audit and portable
packaging of the certificate chain. It is not a Ramsey breakthrough, and the
degree-twelve completion count remains 0/12.

## Reproducibility and storage

Large catalogues, CNFs, logs, samples and LRAT traces live below
`S:\CodexResearchCache\ramsey-formal`; repository code and reports remain
small. The source verification script runs the degree-twelve Python suites
and the relevant Lean targets. External certificate regeneration and LRAT
replay are separate, hash-checked publication steps.

The order-seven cover generator, witness replay, lower-bound kernel and exact
Lean-replay driver are kept in `scripts/r45_d12_gluing_aware_cover/`. Their
heavy generated artifacts remain under
`S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-structural-cover` and
are not duplicated in Git.

Primary references:

- McKay and Radziszowski, *R(4,5)=25*:
  <https://users.cecs.anu.edu.au/~bdm/papers/r45.pdf>
- Gauthier and Brown, *A Formal Proof of R(4,5)=25*:
  <https://drops.dagstuhl.de/storage/00lipics/lipics-vol309-itp2024/LIPIcs.ITP.2024.16/LIPIcs.ITP.2024.16.pdf>
- McKay's Ramsey graph catalogue:
  <https://users.cecs.anu.edu.au/~bdm/data/ramsey.html>
