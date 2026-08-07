# Universal `cover9` experiment

Status: deterministic CNF generated and structurally verified; all 13
two-centre residual CNFs for root degree eight have Lean-replayed LRAT
certificates.  The global semantic bridge and root degrees 3 through 7 remain.

## Statement encoded

The formula has one positive/raw-adjacency variable for each of the 66 edges
of `K_12`.  Its 990 base clauses exclude a clique or independent set of order
four.  For each of the 792 seven-vertex subsets, it then excludes every
labelled copy of the nine records in `cover9.tsv`.  Therefore the formula is
satisfiable exactly when an `R(4,4,12)` graph avoids all nine induced motifs.
This construction reads neither `r44_12.g6` nor a completeness certificate
for that catalogue.

## Safe local reduction

The direct encoding has 26,460 labelled pattern blockers on every subset,
for 20,957,310 clauses including the Ramsey core.  Six partial-pattern
representatives are closed under all `7!` vertex permutations, producing
15,120 distinct local clauses:

| width | clauses |
|---:|---:|
| 14 | 3,780 |
| 15 | 2,520 |
| 16 | 2,520 |
| 18 | 6,300 |

The reduction is conditional on the local `R(4,4)` constraints, not an
unconditional Boolean equivalence.  This condition is available in every
global model: restricting the 990 global Ramsey clauses to any seven-vertex
subset forbids a monochromatic `K4` there.

Both the generator and a separately implemented verifier enumerate all
2,097,152 labelled graphs on seven vertices.  Exactly 923,012 satisfy local
`R(4,4)`.  Among those, the reduced clauses reject exactly the same 26,460
assignments as the nine complete labelled motif orbits, leaving 896,552.  A
test also mutates one bit of a representative and checks that the independent
verifier rejects the corruption.

The reduced global formula has 11,976,030 clauses and 193,602,420 literals.
All local clauses mention all seven vertices, so instantiations belonging to
different seven-subsets cannot be duplicate clauses.

## Frozen SSD artifacts

Directory:
`S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-cover9-universal`

| file | bytes | SHA-256 |
|---|---:|---|
| `cover9_local_reduced.cnf` | 813,795 | `E10B250F2198A569C0A18FDF817B3072CF1266A6B532100AD20F53308296947D` |
| `cover9_universal.cnf` | 701,106,138 | `425676A0876F06BCE2D3477BB6D11A566D77C6DD7D7FD46E9A1B07D8E5C1C098` |

The full file has exactly 11,976,031 lines including its DIMACS header.
Generation took roughly 24 seconds on the current machine.  The repository
contains no large CNF, log, or proof artifact.

## Certification status

The following parts are checked and reproducible:

1. Cover records and labelled orbit cardinalities.
2. Reduced-vs-direct local equivalence over all `2^21` assignments, using two
   independent implementations.
3. Deterministic full CNF size, line count, and SHA-256.
4. Offline restriction, exact deduplication, DIMACS counts, and hashes for the
   root-degree and two-centre targets described below.
5. CaDiCaL-internally-checked LRAT certificates and independent
   LRAT-Catcher/Lean replays for all 13 two-centre degree-eight residual CNFs.

Lean now formalizes the graph-theoretic degree-eight split itself: a genuine
root-fixing permutation, the degree bounds, the normalized second centre, the
exact 13-case disjunction, and transport of `R(4,4)` freeness and motif
occurrence. What is still absent is the semantic bridge from each generated
residual CNF (including offline restriction and exact deduplication) to its
graph branch, followed by composition with the matching replay theorem.
Certificates for root degrees 3 through 7 are also absent. Consequently the
degree-eight residual formulas and their case split are separately certified,
but the universal induced-cover theorem is not yet composed.

## Solver pilots and symmetry restrictions

A proof-free CaDiCaL pilot on the unsymmetrized master timed out after 300.102
seconds.  Parsing took 16.30 seconds; the last flushed row showed 34,940
conflicts at 219.47 seconds.  The ten-clause root-prefix variant has 11,976,040
clauses, 701,106,211 bytes, and SHA-256
`6BD6355400C03874532539D69A49A6FE11AECA11E3C1FB0E8EB6FAC8422A1D3A`.
Its pilot also timed out after 300.126 seconds: parsing took 15.94 seconds and
the last row showed 34,941 conflicts at 204.20 seconds.  The roughly
seven-percent throughput gain was insufficient.

Every vertex of an `R(4,4,12)` graph has degree between 3 and 8.  Permuting
vertices lets us fix the neighbours of root 0 to a prefix for each of the six
degrees.  Exact conditioned local minimization gives these clause totals:

| root degree | first conditioned target | block-conditioned target |
|---:|---:|---:|
| 3 | 5,063,901 | 3,052,941 |
| 4 | 5,105,211 | 3,465,951 |
| 5 | 5,139,690 | 3,508,890 |
| 6 | 5,158,770 | 3,181,470 |
| 7 | 5,156,115 | 2,552,955 |
| 8 | 5,129,421 | 1,750,101 |

The block condition also uses the absence of a positive triangle inside the
root-neighbour block and of a negative triangle inside its complement.  The
generated degree-eight file has 1,750,101 clauses, 104,501,744 bytes, and
SHA-256
`3CE0350607818AEE8CFD3F365316286D2EEC8985FB6A2056953A58FB34DC27DB`.
The earlier degree-three target has 5,063,901 clauses, 306,318,299 bytes, and
SHA-256
`61950D354BAF39450CD0CA4D9972B3C663FB09D9FBFF0BDE4333E125FC73EA5A`.
Its 300.045-second proof-free pilot parsed in 6.75 seconds and reached 62,784
conflicts at 294.66 seconds before timeout.  No pilot in this section emitted
a proof.

## Exact two-centre split of the degree-eight branch

For root degree eight, take vertices 1 through 8 as root neighbours and 9
through 11 as non-neighbours, then choose vertex 1 as a second centre.  Let
`p` count its neighbours in vertices 2 through 8 and `q` those in vertices 9
through 11.  We have `p <= 3`: four common neighbours of adjacent vertices 0
and 1 would have to be pairwise nonadjacent to avoid a positive `K4`, and
would therefore form a negative `K4`.  Also `q <= 3` by block size and
`p + q >= 2` by the minimum-degree bound.  The stabilizer of the first root
sorts the two blocks independently, so the following 13 cases exhaust the
degree-eight branch up to permutation.

| p | q | clauses | bytes |
|---:|---:|---:|---:|
| 0 | 2 | 782,090 | 45,849,047 |
| 0 | 3 | 796,308 | 46,565,434 |
| 1 | 1 | 772,886 | 45,401,795 |
| 1 | 2 | 791,124 | 46,277,854 |
| 1 | 3 | 809,859 | 47,163,820 |
| 2 | 0 | **758,924** | **44,764,698** |
| 2 | 1 | 778,667 | 45,681,042 |
| 2 | 2 | 799,922 | 46,675,347 |
| 2 | 3 | 823,149 | 47,717,807 |
| 3 | 0 | 761,533 | 44,886,711 |
| 3 | 1 | 782,957 | 45,880,826 |
| 3 | 2 | 807,070 | 46,975,647 |
| 3 | 3 | 833,918 | 48,129,797 |

All 13 files are below one million clauses.  The best case, `(p,q)=(2,0)`,
is about 15.78 times smaller in clause count than the master and has SHA-256
`D9CF9356230E6624BED5AB3AC58FACDC98AE96428CF953BD5F8DB1EB3284D315`.
Together the files occupy 601,969,825 bytes on `S:`.  The SSD verifier
recomputed every SHA-256 and line count successfully; the manifest SHA-256 is
`2D62D59D82643B43E218A58CCB762DAF02B6696F5B446D7AC16394B424B55B9A`.
All 13 expected triples `(clauses, bytes, SHA-256)` are also frozen in the
repository tests.

The first proof-free pilot on `(p,q)=(2,0)` returned `UNSATISFIABLE` after
1.12 seconds total, including 1.03 seconds parsing, with only 174 conflicts.
A subsequent bounded sweep returned solver-level UNSAT on all other 12 cases:
65 to 9,704 conflicts and at most 12.70 seconds of search.  The proof-free
batch manifest has SHA-256
`1E7B8CC5A3FC894E24B367F1DFFBFD988D9A92C109D250A99AC51206653AE65E`.
Those pilots motivated, but are logically superseded by, the independently
replayed certificates below.

## Complete exact-CNF certification of the two-centre split

Every case was rerun with CaDiCaL 2.1.2 using `--lrat --no-binary
--checkproof=2 --unsat --walk=false -c 100000`.  Each textual LRAT was then
trimmed and independently replayed by LRAT-Catcher/Lean against the exact
frozen DIMACS file.  All 13 replays returned code zero.  The axiom audit is
case-specific and permits only `propext`, `Classical.choice`, `Quot.sound`,
and the generated `native_decide` axiom whose name is anchored to that exact
`p,q` theorem; `sorryAx` and misleading suffix matches are rejected.

| case | conflicts | LRAT bytes | actions before/after trim | Lean replay s | LRAT SHA-256 |
|---|---:|---:|---:|---:|---|
| p0q2 | 141 | 15,887 | 188 / 57 | 86.598 | `07B0F40D94210713A74C11F16160B6BDDF7F2A1B77C9387E1B97FB397823E215` |
| p0q3 | 134 | 14,867 | 183 / 51 | 88.879 | `DF9777F2FE017D4FB9FAEBE47B17E87200C96B15E7869B3964C306DAE4159FC8` |
| p1q1 | 143 | 14,404 | 218 / 69 | 86.951 | `4A9BE522F1EBF997547660677A6AF95FA04549F9CF7515A89878E49EB0438103` |
| p1q2 | 141 | 15,736 | 189 / 62 | 87.990 | `845B3C828F503398C44EBAA74E244E0F3BD073F9C19D1BABEE5E5303A721BC9F` |
| p1q3 | 65 | 5,969 | 84 / 49 | 89.829 | `7337685653D67A64DC2E394FF18B04A029441E60479CFEE7811FBCD8CD65A467` |
| p2q0 | 174 | 10,683,195 | 201,068 / 285 | 85.316 | `4C65A4480E9BDD8B0F526DE496A774795905C23DD1067D1B4574D267388403C5` |
| p2q1 | 4,339 | 22,522,302 | 402,463 / 10,313 | 90.632 | `80B85075AF6ED1169F8B508A462983D5B200F922644634ACEDCC950EF76A8ABE` |
| p2q2 | 9,206 | 20,737,293 | 378,032 / 22,039 | 91.142 | `9744A5E85A9208A8C731DA5D9814DA951D449B71A6D58CB9BCDE7C0982D82B99` |
| p2q3 | 9,704 | 30,739,229 | 564,461 / 25,860 | 94.028 | `12D7C9A687B49F705EE708C048D68188D49DF08005DC2F9DD052A907C9DA1E47` |
| p3q0 | 3,083 | 35,993,189 | 660,543 / 8,335 | 86.968 | `962EEC6EB178DC42C810EDB02D21E2850B8FDA3E4515991DB7153E7E4F58B491` |
| p3q1 | 4,491 | 25,317,889 | 461,102 / 12,384 | 88.520 | `747EE2845F10FDE0840C4533FE78EFBBF7D13DBF85B0B1C8129CAB883288D7F3` |
| p3q2 | 4,272 | 34,539,054 | 652,249 / 11,485 | 90.077 | `8942BE5A2D5BA16D2EA7ADAA50D1ECEF83D8FB9C5C2B42957F83BDE944B1FA60` |
| p3q3 | 4,948 | 42,141,609 | 755,458 / 13,259 | 92.315 | `5F8A28398B434FF1CAB3906A9591DB0B203063671E17C83D337592821F387BC2` |

The 13 LRAT files total 222,740,623 bytes; the largest is 42,141,609 bytes,
well below the one-GiB guard.  The `(2,0)` proof was generated three times
under the checked recipes and was bit-identical each time.  The lightweight
consolidated manifest `TWO_CENTER_CERTIFICATES.json` has 13 formula/proof/log
identities, exact theorem names and trim statistics; its SHA-256 is
`77FE47B5BC73865EDB0405DFC2D3B0A367C2A757B27A83CDC981D5958F80DE23`.
Its artifact paths are portable and resolve relative to the output directory
supplied to the verifier; no machine-specific absolute cache path is tracked.
The heavy CNFs, LRATs and logs remain exclusively on `S:`.

## Exact complement-closed cover6 follow-up

The earlier eight-class closure prototype has been superseded by an exact
minimum. Three complement pairs, hence six order-seven isomorphism classes,
cover all 1,449,166 records of the frozen official `R(4,4,12)` catalogue.
The TSV SHA-256 is
`404E49E3218424FCB73314ADEE42CC873CD3F8D67E4615653A8BC0210F61AD16`;
the disjoint labelled closure has 25,200 masks and SHA-256
`04B9688924BFC2EF6F92FB5734B19E7E771C37446DD3E442ECED8648BE1CBDD7`.

A standalone lower-bound replay checks 30 explicit `R(4,4,12)` graphs,
reconstructs all `2^21` labelled order-seven graphs and 181 complement pairs,
and excludes all 16,471 selections of at most two pairs. A separate direct
upper replay scans every catalogue record and every seven-subset without
reading the discovery incidence matrix or witness; it finds zero holes.
Therefore six is the exact complement-closed minimum for the frozen
catalogue. The lower bound is absolute on the explicit kernel, whereas the
upper remains catalogue-relative.

For the universal route, two independent implementations verify 25,200
partial cubes closed syntactically under complement, exact on all 923,012
local `R(4,4)` assignments. The cube SHA-256 is
`0239E74AC009B28173E59C3293F7F9C9370A99832B19BB28205EF449E6238F7D`.
Complement symmetry reduces root degrees `3..8` to representatives `6,7,8`;
their conditioned clause counts are respectively 4,858,890, 4,312,419 and
3,367,437. The generated degree-eight formula has 189,298,232 bytes and
SHA-256
`64E411A23778972A85DE7C8613A1977F98115E2EC3C9B1711D129932A4ECBB5A`.
No complete cover6 solver/LRAT certification is claimed at this checkpoint.
## Publication assessment

The work has crossed a genuine certificate threshold: every labelled residual
CNF in the complete two-centre split of the degree-eight target has an
independently replayed Lean/LRAT refutation.  This is a reusable and fully
checkable exact-CNF result, not merely solver evidence.

It has not yet crossed the global combinatorial theorem threshold. The next
proof obligations are (1) a Lean semantic bridge validating local reduction,
offline restriction and exact deduplication for these CNFs, (2) composition of
the 13 replays with the already-formal two-centre case theorem, and (3)
certification of representative degrees 6 and 7 for the sharper
complement-closed cover6 route. Until these are complete, no universal
induced-cover theorem, major mathematical breakthrough, or new Ramsey-number
bound is claimed.