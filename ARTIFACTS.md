# Large proof artifacts

Large generated CNF/LRAT files are intentionally excluded from Git history.
They are preserved in the private Release `checkpoint-2026-08-06` as the
single portable archive:

```text
R55_REPRISE_COMPLET_2026-08-06.zip
SHA-256 2A9C34DBB615CB70FB542B7955FED5C19495EC6DE828C1306778B1DF05ADD571
Size    86,613,268 bytes
```

The ZIP has 116 file members and 115 internally listed SHA-256 entries. Its
CRC, internal hashes, inventory, CNF headers and presence of the final Lean
completeness theorem were checked before upload.

Files kept in the Release rather than Git:

- `r55_n43_base.cnf` — 88,181,670 bytes;
- `min_d20_c10.cnf` — 90,220,831 bytes;
- `min_d20_c10_t0.lrat` — 29,293,939 bytes;
- `hard_d20_c10_t312_reglex_w5.cnf` — 90,268,801 bytes;
- `hard_t312_reglex_w5.lrat` — 116,547,429 bytes;
- bundled Windows CaDiCaL and Elan installers.

After downloading the Release, compare its SHA-256 with
`R55_REPRISE_COMPLET_2026-08-06.zip.sha256.txt`, extract it under a short path,
then run `VERIFY_AND_SMOKE_TEST.ps1 -HashesOnly`.

The release-dependent Lean modules `R55MinLeafBridge.lean` and
`R55MinLeafSemantics.lean` replay the type-0 certificate. To build them from a
Git clone, copy these extracted files into the clone's `r55/` directory:

- `min_d20_c10.cnf`;
- `min_d20_c10_t0.lrat`.

They are intentionally not part of the default lightweight smoke test because
the proof replay takes several minutes and the two artifacts are release-only.
