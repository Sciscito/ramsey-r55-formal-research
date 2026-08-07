# Complement-closed order-seven minimum

For the frozen exhaustive official catalogue of 1,449,166 `R(4,4,12)`
graphs, the minimum size of an order-seven motif cover that is closed under
graph complementation is **six classes**, or three complement pairs:

| official IDs (0-based) | graph6 pair | labelled orbit sizes |
|---|---|---|
| 41, 220 | `F@h^g`, `FKDhw` | 5,040 + 5,040 |
| 174, 323 | ``FG`Xo``, `FdW}w` | 2,520 + 2,520 |
| 185, 194 | `FHFLw`, `FIIXw` | 5,040 + 5,040 |

The six rows form exactly three complement pairs modulo `S7`. Their disjoint
labelled closure has 25,200 masks. The upper bound covers all 1,449,166 frozen
catalogue records. The lower bound is stronger than a catalogue-only search:
30 explicit graphs are checked directly as `R(4,4,12)`, and no choice of at
most two of the 181 complement pairs hits all of them.

Scope matters. The lower bound is absolute for this motif-cover model because
it uses explicit valid graphs. The upper bound is relative to the frozen
official exhaustive catalogue. This is a structural certificate, not by
itself a new Ramsey-number bound, and no literature-priority claim is made.

## Reproduction

Keep external catalogues and generated products on `S:` and disable bytecode:

```powershell
$env:PYTHONDONTWRITEBYTECODE='1'
$env:R45_R44_SOURCE_DIR='S:\CodexResearchCache\ramsey-formal\sources\mckay-r44'
python -B -m scripts.r45_d12_complement_closed_minimum.verify_minimum `
  --source7 "$env:R45_R44_SOURCE_DIR\r44_7.g6"
python -B -m scripts.r45_d12_complement_closed_minimum.verify_cover6 `
  --source12 "$env:R45_R44_SOURCE_DIR\r44_12.g6"
python -B -m unittest `
  scripts.r45_d12_complement_closed_minimum.test_complement_closed_minimum -v
```

`verify_minimum` takes about 16 seconds on the audited machine. The fully
direct stdlib-only upper replay takes about 167 seconds and deliberately reads
neither the 65 MB incidence matrix nor the generated witness.

See `MANIFEST.json` for all frozen hashes and `REPORT.md` for the proof split.
