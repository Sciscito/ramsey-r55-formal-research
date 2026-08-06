# Certified small Ramsey bounds and direct-solver diagnostics

Date: 2026-08-06

Solver: CaDiCaL 2.1.2

Proof format: textual LRAT (`--lrat --no-binary`)

## Green result: `R(4,4) <= 18`

The monolithic encoding of `R(4,4,18)` has 153 variables and 6,120
clauses.  A direct LRAT run was stopped after its incomplete proof reached
2,687,672,320 bytes without deriving the empty clause.  That partial file was
deleted because it was not a certificate.

The checked result instead uses the classical recurrence

`R(4,4) <= R(3,4) + R(4,3) <= 9 + 9 = 18`.

The only solver certificate is the much smaller `R(3,4,9)` refutation:

| item | value |
| --- | ---: |
| variables | 36 |
| clauses | 210 |
| conflicts | 8,937 |
| solver CPU time | 0.09 s |
| LRAT size | 961,008 bytes |
| LRAT lines | 14,360 |

Hashes:

```text
41BDBE084CE9103070848AAF8E5274EF58959CC087C16BC133DF64152A7B58E6  r34_9.cnf
5445D87DE1AAD1EA56B760DAF0483352846ED624AD10DDCC80CC4F50981B9618  r34_9.lrat
```

`RamseyUpperBounds.r34_upper` replays the LRAT certificate.  The fully
formal theorem `RamseyRecurrence.r44_upper_of_r34_upper` proves the recurrence
at the semantic coloring level, including the red/blue complement case.
Together they yield `RamseyUpperBounds.r44_upper`.

## Open certificate: `R(4,5) <= 25`

The direct Lean-generated encoding has 300 variables, 65,780 clauses and
2,417,684 bytes:

```text
734136D3C952A3B6FE8A8A3AB6D3735EA674A93B1C7B4C0394981F5BF8392842  r45_25.cnf
```

Bounded direct runs all ended `UNKNOWN`:

| conflicts | LRAT | CPU time | real time | peak RAM | proof bytes |
| ---: | --- | ---: | ---: | ---: | ---: |
| 100,003 | enabled | 3.86 s | 3.91 s | 33.59 MB | 35,354,152 |
| 1,000,000 | enabled | 38.80 s | 39.64 s | 61.61 MB | 448,054,388 |
| 5,000,000 | disabled | 181.70 s | 184.94 s | 98.77 MB | n/a |

The two partial LRAT traces contain no empty-clause certificate and are not
retained.  At the observed one-million-conflict rate, a monolithic textual
proof already grows by roughly 448 bytes per conflict.  The next appropriate
route is symmetry breaking and/or a formally checked cube cover, not an
unbounded monolithic run.

## Degree consequence already formalized

`R55DegreeBounds.allDegrees_le_twentyFour` proves, parametrically from
`hR45 : not hasRamseyFreeColoring 25 4 5`, that every vertex of a hypothetical
`K_43` coloring with no monochromatic `K_5` has both red and blue degree at
most 24.  The proof selects 25 neighbors, constructs the induced `K_25`
coloring, and complements it in the blue-neighborhood case.
