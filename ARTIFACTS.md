# Large proof artifacts

Large generated CNF/LRAT files are intentionally excluded from Git history.
Each artifact family below is tied to tracked SHA-256 manifests.

## `R(4,5,25)` red-degree-eight guarded-master bundle

The complete certificate consists of 59 leaf LRAT files and one cover LRAT
file: 2,405,113,598 uncompressed bytes. Their canonical names, sizes and
SHA-256 digests are tracked in
`scripts/r45_d8_pilot/guarded_master/proof_bundle_manifest.json` (SHA-256
`C4D7B5E1BD2030090963E30533DC2208CBD15A09A54DD487DEBA9E0FAFBBCB34`).

Four ZIP64/Deflate archives were packed and independently
decompressed and rehashed on 2026-08-06. Their verified container inventory
is tracked in `proof_bundle_archives.json` next to that manifest (SHA-256
`E0B0CF9C75B0D2185B8B2C30C8B12CE89B9277FF680AB80FDDA7806297D4062D`):

```text
202,595,839  08C9BE342A3ADF42044AA041FAB82D970DC519C0CB9E5AF6A476727AD16ABD46  r45-d8-lrat-v1-p01-leaves-01-20.zip
179,153,713  01B52916487237FB6B44A45C62D49F1CA96845D2EBA54A3FEA7E2808471172CC  r45-d8-lrat-v1-p02-leaves-21-22.zip
140,288,173  B03D3EA26EB8DEA13D441527233DC9BDD7B38062DCC3316DA6D2048FF33558B7  r45-d8-lrat-v1-p03-leaves-23-36.zip
125,289,224  16C5782D3F47CC4754A49C1F22C0361111F518959C9C12884D41160D6FB2E5F1  r45-d8-lrat-v1-p04-leaves-37-59-cover.zip
```

The four archives total 647,326,949 bytes. They are prepared for the planned
GitHub Release tag `r45-d8-guarded-master-lrat-v1`, but must not be described
as publicly retrievable until the Release upload and redownload audit have
completed.

After downloading the four ZIP files beside one another, verify them without
extracting:

```powershell
python scripts\r45_d8_pilot\proof_bundle.py verify `
  --manifest scripts\r45_d8_pilot\guarded_master\proof_bundle_manifest.json `
  --archives <external-archive-directory>
```

Install them into an explicit external SSD cache and create the ignored
repository junction only after every member has been verified:

```powershell
python scripts\r45_d8_pilot\proof_bundle.py install `
  --manifest scripts\r45_d8_pilot\guarded_master\proof_bundle_manifest.json `
  --archives <external-archive-directory> `
  --cache <external-SSD-cache-directory> `
  --link
```

For the terminal audit, force Lean to reread the external certificates rather
than trusting a cached `.olean`:

```powershell
cd vendor\lrat-catcher
lake env lean LRATCatcher\Tests\R45DegreeEightGuardedMaster.lean
```

## Earlier `R(5,5)` checkpoint

The large artifacts from the preceding `R(5,5)` milestone are preserved in
the private Release `checkpoint-2026-08-06` as the portable archive:

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
