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
This closes finite CNF reconstruction only. The 13 solver results still have
no LRAT. Lean's `R44Cover6MotifBridge` now decodes the six graph6 motifs,
checks their complement pairs, and proves the full 21-literal blocker
equivalent to a labelled induced occurrence; partial-cube expansion, global
formula equality and branch composition remain open.
