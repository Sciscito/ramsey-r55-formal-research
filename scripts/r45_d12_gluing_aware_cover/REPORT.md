# Five order-seven motifs: exact frozen-catalogue cover and lower bound

## Result

The five raw-graph6 motifs in `cover5_order7.tsv` cover all 1,449,166
records of the frozen official `r44_12.g6` source.  The compact native
incidence has zero holes, and an independent Python replay checked one
explicit induced-subgraph witness for every record using the full labelled
7! closure of each motif.

The five motifs are:

| graph6 | edges | holes if removed |
|---|---:|---:|
| `F@h^g` | 11 | 30 |
| `FCUrO` | 9 | 18 |
| `FDLmW` | 11 | 46 |
| ``FG`Xo`` | 8 | 159 |
| `FdW}w` | 13 | 90 |

This is cardinality-minimal among **order-seven** R(4,4) motifs for the
frozen order-twelve catalogue.  A 25-graph subset has no hitting set of at
most four order-seven motifs.  That lower bound was checked three ways:

1. all 2^21 labelled order-seven graphs were enumerated; exactly 923,012
   are R(4,4) graphs, matching the labelled closure of all 362 official
   unlabelled records;
2. an independent decoder recomputed all 792 induced seven-vertex subsets
   of each of the 25 explicit order-twelve witnesses;
3. both an exhaustive 147,127-state hitting-set search and a dedicated
   Lean/LRAT-Catcher theorem
   `R45OrderSevenCoverMinimumReplay.no_order7_cover_of_size_four` reject
   cardinality at most four.

The lower bound uses explicit graphs and does not require completeness of
the order-twelve catalogue.  The upper bound remains catalogue-relative
unless that catalogue's completeness is supplied independently.  No
minimality is claimed when order-eight motifs are also allowed, and this is
not an R(4,5,25) unsatisfiability proof.

## Frozen hashes

| artifact | SHA-256 | bytes |
|---|---|---:|
| `cover5_order7.tsv` | `CEAE61F737722C6D1392B5C8D654FC1B09D482AA3C76222EE2D9CBFF3CA5E288` | repository file |
| compact incidence | `38E61DABA2597AAADC0821F6738059091FAAAFF7F97968D094EDA17826A8510E` | 905,936 |
| induced witness | `36EC5E95D8599F6AE8099A6D3376D0E3F43269059FC644A1A3F96C52846414CB` | 4,347,650 |
| 25-graph kernel report | `46BA1FEA2EB4415DD96C602074AD393B471876ED2FA7A1DBE4AE5EC24A19785D` | 53,654 |
| no-cover4 CNF | `84E1BE500A85AD2B6F63F780063116F4AF0DE3239C63710AFF8816057AC6EF82` | 49,015 |
| no-cover4 LRAT | `4FD1F02297F5019B9EADBE9BC20E29DF326B0B7F99B8A539C140FD9911F15793` | 38,438,129 |
| dedicated Lean replay report | `DB075E5F11E664386B845131F1F6DECBFAB3B7832D107CA314029C773338A4F9` | 1,366 |

Heavy artifacts are under
`S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-structural-cover`.
They are intentionally not tracked by Git.

## External upper-cover replay

The dedicated replay test is optional and skips cleanly when its external
artifact environment is unset:

```powershell
python -m unittest scripts.r45_d12_gluing_aware_cover.test_cover5_external_replay -v
```

The full frozen replay uses the following paths without copying the heavy
artifacts into the repository:

```powershell
$env:R45_R44_SOURCE_DIR = 'S:\CodexResearchCache\ramsey-formal\sources\mckay-r44'
$env:R45_R44_ORDER7_INCIDENCE = 'S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-structural-cover\incidence_all_order7_full.bin'
$env:R45_R44_COVER5_WITNESS = 'S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-structural-cover\cover5_order7_witness.bin'
python -m unittest scripts.r45_d12_gluing_aware_cover.test_cover5_external_replay -v
```

Checkpoint execution on 2026-08-07 gave `OK (skipped=1)` without the
variables and `OK` in 20.912 seconds with the frozen `S:` paths.

It runs `cover_audit.verify` before `verify_mixed_witness.verify` and requires
1,449,166 entries, zero uncovered catalogue records, the exact irredundancy
holes, and every frozen source/cover/incidence/witness hash.

## Gluing benchmark

Fixing each motif on the first seven vertices of the d12 B block leaves the
frozen type-0 SAT leaf unresolved in raw DIMACS polarity:

| conflict budget | result |
|---:|---|
| 100,000 per motif | 5/5 UNKNOWN |
| 200,000 per motif | 5/5 UNKNOWN |

These are proof-free strategy measurements.  The structural minimum reduces
the number of gluing cases from nine to five.  The earlier cover9 benchmark
also remained 9/9 UNKNOWN even at one million conflicts per motif; because
the budgets differ, this comparison establishes a case-count reduction, not
a solver-speed improvement.  No degree-twelve SAT leaf has been closed.
