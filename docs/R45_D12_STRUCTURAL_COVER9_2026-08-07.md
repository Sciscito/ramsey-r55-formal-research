# Exact nine-motif structural cover at degree twelve

Date: 2026-08-07

> **Checkpoint addendum.** Cover9 remains a valid witnessed nine-motif
> catalogue cover, but it is no longer the cardinality frontier. The
> unrestricted order-seven minimum is five. Under complement closure the exact
> minimum is six classes/three pairs, with zero holes on the same frozen
> catalogue and an independent 30-graph lower-bound kernel. Separately, the
> catalogue-independent cover9 degree-eight split now has 13/13 exact CNF
> LRAT refutations replayed in Lean plus a formal graph-level 13-case split.
> The CNF semantic bridge, replay composition and other degrees remain open.

## Result

An exact replay over McKay's frozen `R(4,4,12)` data verifies:

> Every one of the 1,449,166 catalogue representatives contains an induced
> copy, in raw graph6 adjacency, of at least one of nine fixed
> `R(4,4,7)` representatives.

The motifs are:

| id | graph6 | edges | labelled closure | incidence | holes if removed | witnesses |
|---:|:---|---:|---:|---:|---:|---:|
| 0 | `FiIXw` | 11 | 5,040 | 1,439,206 | 6 | 396,157 |
| 1 | `FANbw` | 11 | 2,520 | 1,333,405 | 50 | 247,776 |
| 2 | `F@Y]w` | 11 | 5,040 | 1,406,032 | 12 | 256,312 |
| 3 | `FqhXw` | 12 | 2,520 | 1,423,783 | 9 | 124,548 |
| 4 | `FFhmw` | 13 | 2,520 | 1,112,269 | 1 | 7,806 |
| 5 | `FqHXw` | 11 | 2,520 | 1,275,634 | 5 | 260,279 |
| 6 | `FQl~_` | 13 | 2,520 | 1,270,258 | 1 | 30,476 |
| 7 | `FIiZw` | 12 | 2,520 | 1,268,997 | 1 | 107,174 |
| 8 | `Fqoxw` | 12 | 1,260 | 1,031,848 | 1 | 18,638 |

Their union has zero holes. Deleting the motifs in displayed order leaves
`[6, 50, 12, 9, 1, 5, 1, 1, 1]` holes, so this cover is irredundant. There is
no claim that nine is the minimum possible cardinality.

## Certificate chain

The native scanner constructs complete labelled isomorphism closures and
tests all 792 induced seven-subsets of every catalogue graph. The final scan
took about 25 seconds and wrote a 1,630,640-byte incidence file, SHA-256
`D5E50DFF135023BF934D75078DDA74173C182EDB49B7048B207A6A1046EB83BC`.

It also wrote one explicit `(motif id, subset id)` witness per catalogue
record. This certificate is 4,347,738 bytes, SHA-256
`A5C8BFC67618FB5345AD072E07237271390068B0883C12B04D4B0BEE4E379B96`.
An independent Python checker, with a separate graph6 decoder and no use of
the scanner's `PEXT` implementation, rebuilt every 7! closure and directly
checked all 1,449,166 witnesses in 15.8 seconds. Status: `PASS`. A corrupted
copy was rejected.

A separate synthetic cross-check compared the native incidence output to a
pure-Python exhaustive permutation oracle for mixed order-7/order-8 motifs
and sparse, non-contiguous subsets. Every bit agreed and padding bits were
zero.

The exact edge-complement list was then replayed independently over the full
catalogue in 23.1 seconds. It also has zero holes; its incidence SHA-256 is
`D2B2330FBDE43AD96C5435C9F0AC8DF4B444813C694E7A69C5A226684E9FDD0B`.
This closes a dangerous convention ambiguity at the structural layer.

## Frozen inputs

| catalogue | records | SHA-256 |
|:---|---:|:---|
| `r44_7.g6` | 362 | `6A3DA7F0687C392420F190DB0643B5C5B7ECB1A3C5ED098C7D96200185A5F010` |
| `r44_8.g6` | 2,079 | `B27389F7B1C70F823161A2CCA629BED3F4FBF058A43907637C0F9CE2E0CC4AB3` |
| `r44_12.g6` | 1,449,166 | `C6A60EE177E00C1168259A5BD464F9CFA5A5B471AE2BA1811E7B3FAF23144E7A` |

All large inputs and products live under
`S:\CodexResearchCache\ramsey-formal`; the Git repository contains only
small source, manifests and reports.

## Colour orientation

The checked relation is literal graph6 adjacency. The current DIMACS import
maps an edge to a positive/red literal. The historical HOL4 numbering uses
`1 = blue` and `2 = red`. Opposite conventions are related only through the
explicit complement list; raw and complemented motifs must not be silently
interchanged in a SAT leaf or Lean bridge.

## Historical and publication assessment

McKay and Radziszowski reported in 1995 that they selected 23 order-7 and 51
order-8 graphs, favouring dense patterns for their gluing computation. Their
paper does not print the 74 records. The nine-pattern list above was found
independently by a cardinality-oriented search. A limited search of indexed
sources found no prior match, but that bibliographic and archival audit is
incomplete. We therefore do not claim that this is the historical list or
that the compact cover is unprecedented.

Scientifically, this is a compact and reproducible certificate artifact, but
it is not the current cardinality frontier: a seven-motif candidate was found
after this witness was frozen and is being validated separately. This report
therefore records the cover9 certificate chain, not a publication-threshold
claim. It does not certify the completeness of the external catalogue inside
our trusted base, and it does not show that the nine corresponding
`R(4,5,25)` gluing/SAT branches are tractable or unsatisfiable. The
degree-twelve branch remains open.

The most direct route to a catalogue-independent theorem is a 66-variable CNF
asserting `R(4,4,12)`-freeness and avoidance of all nine induced motifs. The
nine isomorphism closures contain 26,460 labelled masks. Across 792
seven-subsets this gives 20,956,320 blocking clauses; with 990 Ramsey clauses,
the direct formula has exactly 20,957,310 clauses. It has been sized but has
not yet been generated, solved or LRAT-certified.

## Reproduction entry points

- `scripts/r45_d12_structural_cover/r44_cover_scan.c`: native full scanner;
- `scripts/r45_d12_structural_cover/verify_cover9.py`: frozen incidence audit;
- `scripts/r45_d12_structural_cover/verify_witness.py`: independent witness audit;
- `scripts/r45_d12_structural_cover/cross_check.py`: native/oracle cross-check;
- `scripts/r45_d12_structural_cover/COVER9_MANIFEST.json`: exact inventory;
- `scripts/r45_d12_structural_cover/README.md`: commands and formats.

Primary references:

- McKay--Radziszowski, *R(4,5)=25*: <https://users.cecs.anu.edu.au/~bdm/papers/r45.pdf>
- McKay's Ramsey graph data: <https://users.cecs.anu.edu.au/~bdm/data/ramsey.html>
- Gauthier--Brown, *A Formal Proof of R(4,5)=25*: <https://drops.dagstuhl.de/storage/00lipics/lipics-vol309-itp2024/LIPIcs.ITP.2024.16/LIPIcs.ITP.2024.16.pdf>
