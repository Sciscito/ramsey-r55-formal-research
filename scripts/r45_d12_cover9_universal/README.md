# Catalogue-independent universal target for `cover9`

This directory builds a SAT statement that does **not** assume that the
published `r44_12` file is a complete catalogue.

There are 66 Boolean edge variables for `K_12` (positive means raw graph6
adjacency).  The first 990 clauses forbid a `K4` and an independent `K4`.
For every one of the 792 seven-vertex subsets, further clauses exclude the
nine patterns in `../r45_d12_structural_cover/cover9.tsv` up to every vertex
permutation.  Consequently, UNSAT would prove directly that every
`R(4,4,12)` graph contains one of the nine induced patterns.

The literal encoding has 20,957,310 clauses.  The generator uses six orbits
of partial assignments instead.  It exhaustively enumerates all `2^21`
labelled graphs on seven vertices and checks that, under the local `R(4,4)`
clauses, the resulting 15,120 local clauses reject exactly the same 26,460
labelled patterns.  All reduced clauses use all seven vertices and there are
no cross-subset duplicates.  The global target has 11,976,030 clauses.

Run the solver-free audit with:

```powershell
python -B scripts\r45_d12_cover9_universal\generate_universal.py preflight
```

Generate the large CNF only on the SSD:

```powershell
python -B scripts\r45_d12_cover9_universal\generate_universal.py generate `
  --output S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-cover9-universal
```

The stronger deterministic restrictions are implemented as Python modules
because they use package-relative imports.  For example:

```powershell
python -B -m scripts.r45_d12_cover9_universal.generate_block_degree_branch counts
python -B -m scripts.r45_d12_cover9_universal.generate_two_center_branches verify `
  --output S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-cover9-universal
```

The block-conditioned degree-eight target has 1,750,101 clauses.  Splitting
it at a second centre gives 13 exhaustive cases, all below one million
clauses; the smallest has 758,924.  Exact sizes and SHA-256 values are frozen
in `generate_two_center_branches.py` and summarized in `REPORT.md`.

All 13 exact residual CNFs now have CaDiCaL LRAT refutations independently
replayed by LRAT-Catcher/Lean.  The lightweight, portable identities and
replay metadata are frozen in `TWO_CENTER_CERTIFICATES.json`; the CNFs, logs, and proofs stay
on `S:` and are never tracked in Git.  Rehash every external artifact and
compare the recomputed consolidation with the tracked manifest using:

```powershell
python -B -m scripts.r45_d12_cover9_universal.consolidate_two_center_certificates `
  --output S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-cover9-universal `
  --verify-manifest scripts\r45_d12_cover9_universal\TWO_CENTER_CERTIFICATES.json
```

This certifies all 13 residual CNFs in the complete degree-eight two-centre
split as exact CNF UNSAT. Lean separately proves the graph-level root
permutation, degree bounds, two-centre normalization, exact 13-case
disjunction, and transport of `R(4,4)` freeness and induced motifs. It is not
yet the global universal induced-cover theorem: the remaining obligations are
the CNF semantic bridge (including restriction and deduplication), composition
of each replay with the corresponding graph branch, and root degrees 3
through 7.

## Complement-closed `cover6`, degree eight

The degree-eight complement-closed route is a separate target in this same
directory. Its source has 3,367,437 clauses and its two-centre split has 13
residuals. `exact_replay_cover6_d8.py` is a standalone deterministic
reimplementation: it imports no project generator, checks all `2^21` local
assignments, reconstructs the ordered source, recomputes every reduction and
compares all frozen DIMACS files byte for byte. It deliberately shares the
frozen motif representatives and expected hashes, so it is not a
low-common-mode independent derivation.

```powershell
python -B -m scripts.r45_d12_cover9_universal.exact_replay_cover6_d8 preflight
python -B -m scripts.r45_d12_cover9_universal.exact_replay_cover6_d8 all `
  --artifact-root S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-cover5-closed-universal
```

The portable report is `COVER6_D8_SEMANTIC_REPLAY_V1.json`, SHA-256
`5D8D129A2431B7F473AF24B4BE21864FA6CCBE05DB4D347665FCE0749EB35024`.
This closes finite CNF reconstruction only. The 13 separate residual solver
results still have no LRAT; the single `Master8` route described below now
does. Lean's `R44Cover6MotifBridge` decodes the six graph6 motifs,
checks their complement pairs, and proves the full 21-literal blocker
equivalent to a labelled induced occurrence.

The separate compact Python certificate
`COVER6_CUBE_MOTIF_BRIDGE_V1.json`, associated with
`certify_cover6_cube_motif_bridge.py`, checks that each of the six cube
representatives has one `R(4,4)` completion and that `S7` transports them
bijectively to 25,200 cubes and 25,200 distinct motif masks. It also reduces
root-free conditioning to 334 stabilizer-orbit representatives and
root-containing projected conditioning to 38. This analysis imports
`exact_replay_cover6_d8`; its stated scope contains no SAT, LRAT,
parsed-DIMACS equality, Lean replay, or `cover6-d8` theorem.

`R44Cover6CubeBridge` compiles in Lean and proves the generic partial-blocker
polarity plus a safety-to-occurrence interface. `R44Cover6RepresentativeCubes`
also compiles and certifies all six representatives: well-formedness, their
16--64 completions, the unique `R(4,4)` completion, and the explicit motif
permutation. `R44Cover6S7Transport` now proves generic `S7` invariance of
`R(4,4)`, bit masks and `CubeMatchesLocal`, and transports each representative
proof to any cube carrying an orbit witness. The final local data bridge
is now represented by `COVER6_CONDITIONED_ORBIT_WITNESSES_V1.json`: 32,880 K7
witnesses and 1,200 projected-K6 lift witnesses, packed at 15 bits per row.
Its exhaustive test checks all 34,080 rows and the exact core-ordered view of
3,514 K7 plus 2,409 K6 blockers. `R44Cover6ConditionedWitnesses` decodes that
tracked payload inside Lean, checks the core clauses and lifts with two
aggregated `native_decide` certificates, and constructs the semantic witness
provider. Lean checks all 5,923 decoded semantic equalities used by the proof;
the JSON byte identity, alphabet and metadata are pinned separately by the
Python tests rather than re-authenticated by the Lean parser.

`master8_prefix_pilot.py` constructs a single bounded master formula from
`F8`, 11 root units, eight prefix clauses, and three arithmetic-bound clauses.
An exhaustive audit of the ten second-centre variables gives exactly the 13
historical `(p,q)` assignments. The tracked fingerprint is 3,367,459 clauses,
189,298,375 bytes, SHA-256
`3E725132C29E1CAA9D5FD5EA0AD67D8A5A80E61A1241768D36A910DD23FD329D`.
CaDiCaL 2.1.2 returned UNSAT after 4,598 conflicts and emitted one
128,131,809-byte LRAT, SHA-256
`B2ECDACD2D99CD6EA2929C0B370C6AAFD74FE78FDE20FFBDFE68B7D0EF860505`,
with internal proof checking enabled. A direct Lean replay was stopped at the
3 GiB memory limit before producing a theorem. A conservative RUP dependency
closure then reduced the frozen pair to 6,152 initial clauses and 7,061 proof
additions. The tracked core CNF is 292,093 bytes; its densely remapped LRAT is
754,043 bytes. LRATCatcher replays that proof and a second 777,661-byte LRAT
regenerated by CaDiCaL on the same core. The 6,152-row mapping is checked as an
exact ordered subsequence of the frozen Master8 DIMACS stream. See
`master8_core/MANIFEST.json` for hashes and the exact trust boundary.

`R44Cover6Master8CoreBridge` separately proves generic UNSAT monotonicity for
a lazily indexed CNF source. `R44Cover6Master8IndexedSource` now supplies that
source by four exact sections and combinatorial unranking, checks the 6,152
selected clauses against the replayed core, and proves `master8Source_unsat`.
Core taxonomy then removes the obsolete 13-case structure from the critical
path: only seven sorting clauses and `-15` occur. The resulting `F8 + core8`
source has 3,367,445 clauses, 189,298,301 bytes, SHA-256
`0133D40DC0458E7CD426F22DA08B525B4197467E539E4446AE94A38E84D7341E`,
and Lean proves `normalizedSource_unsat`.

`R44Cover6SemanticComposition` now proves the 717 base clauses and eight
extras, checks the core split `221 + 3514 + 2409 + 8`, and derives a
contradiction with `normalizedCoreSelection_unsat` from an explicit
`CoreBlockerWitnessProvider`. `R44Cover6ConditionedWitnesses` supplies that
provider and proves `degreeEight_has_cover6_motif`: every `R(4,4)`-free
colouring on 12 vertices whose positive root degree is eight contains an
induced copy of one of the six cover6 motifs. This closes `cover6-d8` at local
proof level 4. It does not cover degrees six or seven, the global gluing
argument, or any new Ramsey-number bound. The original solver and failed
full-replay metadata remain frozen in `MASTER8_LRAT_CHECKPOINT_V1.json`.

## Complement-closed `cover6`, degree seven

`R44Cover6DegreeSevenMinCenter` now proves in Lean that a positive-degree-seven
root, after root sorting, has a neighbour whose internal degree in the
seven-vertex positive neighbourhood is one or two. The exact final module
SHA-256 is
`16448C8ECA7D22DDAAF734C481553A750FE1857D23F8288C180EECB2759DB6AF`;
`R44Cover6DegreeSevenNormalization` now moves that witness to label one,
sorts the remaining `6+4` vertices, derives the nine cases and proves the
exact nine DIMACS clauses. Its SHA-256 is
`D9A0BABC4DACDE65404E0C719DF076B2EAC5D0362D5698B8BE8E4F3A34207679`.
`R44Cover6DegreeSevenR34Normalization` closes the wrapper, obtains one of the
nine exhaustive `R(3,4;7)` catalogue representatives, lifts the inverse
catalogue isomorphism to twelve vertices while fixing the root and the opposite
block, and proves the exact 21 branch units. Its SHA-256 is
`1CF0DA9E2B47ED6F502AD1A7701F06D04E36C3DEA9BBE995825B8C1C4FA996B2`.
`R44Cover6Master7R34IndexedSource` then defines lazy exact F7 and nine exact
21-unit branch sources; its SHA-256 is
`6B1650D87BE0F4CC931DF21F180C48451097180D6DFBE09866A0C0B8FCB25A60`.

`audit_cover6_d7_min_center_source.py` independently reconstructs the new K7
`a=3` and projected-K6 `a=2` sections, reuses the audited d8 suffixes, and
streams both F7 and the exact nine-clause Master7 without writing a CNF. The
tracked formula hashes are
`85A93BEEA81BC890E3343A5A52094380446432F81AF9B28A2A35F9B76CAC920C`
for 4,312,419-clause F7 and
`DFA3F7C3C1ADF2F6C8855FA5F08D11D54BFC826205246E68DAD5F4F5D46A5BBE`
for the 4,312,428-clause Master7. A separate
materializer reproduced those exact bytes on `S:`.

A bounded CaDiCaL pilot without LRAT returned `UNKNOWN` at 100,003 conflicts
after 263.82 seconds, with 927.67 MiB maximum resident memory reported by the
solver. `MASTER7_MIN_CENTER_PILOT_V1.json` freezes the command, hashes and
limits. The budget was not raised. Instead,
`materialize_cover6_d7_r34_catalogue_icnf.py` writes one exact incremental F7
stream followed by the nine exhaustive `R(3,4;7)` representatives modulo
`S7`. CaDiCaL closes all nine cubes without a proof in 16,893 conflicts and
29.16 seconds; `MASTER7_R34_CATALOGUE9_PILOT_V1.json` records the exact
metrics and hashes. `R44Cover6DegreeSevenR34Oracle` closes ``FG`Xo`` directly
as an induced cover6 motif, with no SAT certificate. The first nontrivial
certified leaf, ``F`GOW``, has a tracked all-RUP core with 5,807 initial clauses
and 9,475 derived additions. Its compact LRAT replays in Lean in 2.99 seconds at
about 200 MiB. The portable manifest is
`master7_r34_fgravegow_core/MANIFEST.json`, SHA-256
`8A7E66C31F1AF2E8BA81F4FE765D6D1D1EAC2C457EB8FCEB80C1DCC1313C1409`.
`R44Cover6Master7R34FgraveGowCore`, SHA-256
`3266F3DACE0854B665FA2374B0742D5FA0BBD0D4AB79B49BC32DDA21A4320C29`,
checks that the exact 5,807 indices select this core from the lazy F7+21 branch
source and replays the LRAT. `R44Cover6Master7R34FgraveGowSemantics`, SHA-256
`9608990A7CD482A3526E7A7A788D8ED158F3FF3C34E9AA57087B331A4BB20493`,
packs 5,623 witnesses for the exact `168 + 3227 + 2396 + 16` selected clauses,
proves their semantics under the relabelled colouring, and composes them with
the compact UNSAT core to close the ``F`GOW`` leaf. `FoDPO` is the second
closed nontrivial leaf: its portable core contains 7,686 initial clauses and
12,107 RUP additions, while 7,485 witnesses certify the exact
`183 + 4221 + 3264 + 18` selected clauses. The tracked replay passes and
`R44Cover6Master7R34FoDPOSemantics` composes the branch to contradiction in
593.87 seconds under a 600-second cap. `FCUj_` has a separately replayed
1,104-clause core and 990 witnesses; its semantic composition closes in
82.26 seconds. Five nontrivial
representatives, composed catalogue transport and the terminal cover6-d7
theorem remain. No new Ramsey bound is claimed.

```powershell
python -B -m scripts.r45_d12_cover9_universal.certify_cover6_cube_motif_bridge check
python -B -m unittest scripts.r45_d12_cover9_universal.test_cover6_conditioned_orbit_witnesses
python -B -m scripts.r45_d12_cover9_universal.master8_prefix_pilot preflight
python -B -m scripts.r45_d12_cover9_universal.audit_cover6_d7_min_center_source quick
python -B -m unittest scripts.r45_d12_cover9_universal.test_materialize_cover6_d7_min_center_master
python -B -m scripts.r45_d12_cover9_universal.materialize_cover6_d7_r34_catalogue_icnf preflight
python -B -m unittest scripts.r45_d12_cover9_universal.test_master7_r34_catalogue9_pilot
python -B -m unittest scripts.r45_d12_cover9_universal.test_reduce_cover6_d7_r34_fgravegow_lrat_core
python -B -m unittest scripts.r45_d12_cover9_universal.test_master8_core_taxonomy
cd vendor/lrat-catcher
lake env lean LRATCatcher/Tests/R44Cover6CubeBridge.lean
lake env lean LRATCatcher/Tests/R44Cover6RepresentativeCubes.lean
lake env lean LRATCatcher/Tests/R44Cover6Master8CoreBridge.lean
lake env lean LRATCatcher/Tests/R44Cover6Master8IndexedSource.lean
lake env lean LRATCatcher/Tests/R44Cover6S7Transport.lean
lake env lean LRATCatcher/Tests/R44Cover6SemanticComposition.lean
lake env lean LRATCatcher/Tests/R44Cover6ConditionedWitnesses.lean
lake env lean LRATCatcher/Tests/R44Cover6DegreeSevenMinCenter.lean
lake env lean LRATCatcher/Tests/R44Cover6DegreeSevenNormalization.lean
lake env lean LRATCatcher/Tests/R44Cover6DegreeSevenR34Normalization.lean
lake env lean LRATCatcher/Tests/R44Cover6Master7R34IndexedSource.lean
lake env lean LRATCatcher/Tests/R44Cover6DegreeSevenR34Oracle.lean
lake env lean LRATCatcher/Tests/R44Cover6Master7R34FgraveGowCore.lean
lake env lean LRATCatcher/Tests/R44Cover6Master7R34FgraveGowSemantics.lean
lake env lean LRATCatcher/Tests/R44Cover6Master7R34FoDPOCore.lean
lake env lean LRATCatcher/Tests/R44Cover6Master7R34FoDPOSemantics.lean
lake env lean LRATCatcher/Tests/R44Cover6Master7R34FCUjCore.lean
lake env lean LRATCatcher/Tests/R44Cover6Master7R34FCUjSemantics.lean
lake env lean ../../scripts/r45_d12_cover9_universal/master8_core/Replay.lean
lake env lean ../../scripts/r45_d12_cover9_universal/master7_r34_fgravegow_core/Replay.lean
lake env lean ../../scripts/r45_d12_cover9_universal/master7_r34_fodpo_core/Replay.lean
lake env lean ../../scripts/r45_d12_cover9_universal/master7_r34_fcuj_core/Replay.lean
```

Set `RAMSEY_COVER6_BRIDGE_FULL=1` for the exhaustive test that regenerates and
exactly compares the compact cube/motif report. Set
`RAMSEY_COVER6_CONDITIONED_WITNESSES_FULL=1` for all 34,080 conditioned witness
rows. The Master8 core test module documents its three opt-in full audits.
