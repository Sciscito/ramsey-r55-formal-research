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

## Small Ramsey artifacts kept in Git

The compact `R(3,4) ≤ 9` certificate is intentionally versioned because it is
small enough for ordinary source verification:

```text
41BDBE084CE9103070848AAF8E5274EF58959CC087C16BC133DF64152A7B58E6  r34_9.cnf
5445D87DE1AAD1EA56B760DAF0483352846ED624AD10DDCC80CC4F50981B9618  r34_9.lrat
```

The generated `r45_25.cnf` is also versioned as a reproducible diagnostic
input (SHA-256
`734136D3C952A3B6FE8A8A3AB6D3735EA674A93B1C7B4C0394981F5BF8392842`).
It is **not** accompanied by a claimed proof: all bounded runs ended
`UNKNOWN`, and their incomplete LRAT traces were deliberately excluded.
