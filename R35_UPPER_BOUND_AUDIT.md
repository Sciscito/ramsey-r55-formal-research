# R(3,5) ≤ 14 catalogue audit

Date: 2026-08-06 (Europe/Paris)

## Result

Lean exposes the closed theorem:

```lean
LRATCatcher.Tests.R35.r35_upper_catalogue :
  ¬ LRATCatcher.Ramsey.hasRamseyFreeColoring 14 3 5
```

This is the classical upper bound `R(3,5) ≤ 14`, now proved inside this
repository from the exhaustive graph catalogue.  It is a major new certified
dependency for this repository, not a claim of a new mathematical bound in
the literature.

## Independent data audit

The Python verifier was run on the extended JSON certificate and all graph6
catalogues through the empty order-14 level:

```text
python catalog_certificate.py verify . r35_extension_certificate.json
{catalogue_graphs: 1030, max_order: 14, valid_extensions: 10089}
```

Catalogue sizes at orders 11, 12, 13, and 14 are respectively 105, 12, 1,
and 0.  Their valid one-vertex transition counts are 1045, 54, 1, and 0.

`catalog_certificate.py write-lean-data` regenerated
`R35CatalogData.lean` from the extended JSON and graph6 files.  The regenerated
file was bit-identical to the recovered file:

```text
SHA256 6E6625952949378C502E7DC271612559F77DB19E85FD0FC7153FB544345E2AAF
```

Relevant input hashes:

```text
81928570768E2CCC3B12CD056AA40D43596F0482224359D9873BEEC823DFE79F  catalog_certificate.py
2E3A8443F50D35155271D5326D4C6BCEABE461D8B5AEECB9105D487F6CCA6626  r35_extension_certificate.json
D5C52B2209E25080868ADEEF2DD52FA32835E5143208ACEEF129332C9184F16E  r35_11.g6
322E7A54E67F4201BD37998AB420AFB3EEE41B1DCD6B277B7F055BDA152DA95E  r35_12.g6
EB4D3F787F07ED14C0A82A83BEE170ED096C24B6A7E971FDED185CA1A760798F  r35_13.g6
E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855  r35_14.g6
```

The last hash is the standard SHA-256 of the empty file, as expected for the
empty order-14 catalogue.

## Native evaluator crash and repair

Before the proof changes, importing `R35CatalogData` reproducibly exited with
Windows status `-1073741819` (`0xC0000005`) in about 0.5 seconds.  Compiling
the data source itself succeeded.  A fresh OLean compilation differed from
the crash-era cache:

```text
crash-era R35CatalogData.olean: 100170528 bytes
fresh     R35CatalogData.olean: 100170480 bytes
```

The old cache was saved reversibly and the fresh OLean installed.  A minimal
import then succeeded.  The monolithic catalogue computation was additionally
split into one native audit per catalogue level and transition; the global
theorem is recomposed propositionally from those audited pieces.

## Lean verification

Exact final command:

```text
lake build LRATCatcher.Tests.R35CatalogCheckpoint LRATCatcher.Tests.R55TypedUnitsBridge
```

Final status:

```text
Build completed successfully (27 jobs).
```

The checkpoint prints all of the following interfaces:

```text
r35_catalogue_order_fourteen_complete :
  StrongCatalogueComplete 14 (catalogues.getD 14 [])
no_graph_valid_at_fourteen : ¬ ∃ graph, GraphValidAt 14 graph
r35_upper_catalogue : ¬ Ramsey.hasRamseyFreeColoring 14 3 5
```

`#print axioms r35_upper_catalogue` contains the expected Lean logical axioms,
`Classical.choice`, and the named `native_decide` audit axioms.  It contains
neither `sorryAx` nor an admitted theorem.

## Meaning for the R(5,5) project

The theorem is not itself a proof of `R(5,5) = 43`.  It supplies a reusable,
machine-checked small Ramsey upper bound and validates the complete R(3,5)
catalogue chain used to classify common-neighbourhood types.  It therefore
reduces trust in external enumeration and strengthens future degree/codegree
and recurrence arguments in the main R(5,5) search.
