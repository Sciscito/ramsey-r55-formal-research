# Gluing-aware order-seven cover

`REPORT.md` records the exact catalogue-relative five-motif cover, its
order-seven minimum certificate, frozen hashes, and scientific scope.

The external upper-bound replay is optional because its source catalogues,
full order-seven incidence, and induced witness remain on `S:`. With none of
the variables below set, the dedicated test skips without reading external
artifacts:

```powershell
python -m unittest scripts.r45_d12_gluing_aware_cover.test_cover5_external_replay -v
```

To run the full replay against the frozen artifacts:

```powershell
$env:R45_R44_SOURCE_DIR = 'S:\CodexResearchCache\ramsey-formal\sources\mckay-r44'
$env:R45_R44_ORDER7_INCIDENCE = 'S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-structural-cover\incidence_all_order7_full.bin'
$env:R45_R44_COVER5_WITNESS = 'S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-structural-cover\cover5_order7_witness.bin'
python -m unittest scripts.r45_d12_gluing_aware_cover.test_cover5_external_replay -v
```

The test first runs `cover_audit.verify` on `cover5_order7.tsv`, then runs
`verify_mixed_witness.verify`. It requires 1,449,166 catalogue entries, zero
uncovered entries, the exact five records and irredundancy holes, and the
frozen source, cover, incidence, and witness SHA-256 values.
