# Nine-motif structural cover of R(4,4,12)

The exact full-catalogue result is:

> Every one of the 1,449,166 frozen R(4,4,12) catalogue records contains,
> in raw graph6 adjacency, an induced copy of one of nine fixed R(4,4,7)
> motifs.

The list is **cover9.tsv**. Its union has zero holes. Removing the nine motifs
one at a time leaves [6, 50, 12, 9, 1, 5, 1, 1, 1] holes, so the displayed
cover is irredundant; minimum cardinality is not claimed.

This directory freezes the fully witnessed cover9 artifact. It is not the
current cardinality frontier: a separately certified unrestricted
order-seven cover has exact minimum five, and the exact minimum under
complement closure is six classes (three pairs). Cover9 remains important
because its catalogue-independent degree-eight residual split has 13/13
Lean-replayed LRAT refutations; the global semantic composition is still open.

The full native incidence is 1,630,640 bytes with SHA-256
D5E50DFF135023BF934D75078DDA74173C182EDB49B7048B207A6A1046EB83BC.
The explicit witness certificate is 4,347,738 bytes with SHA-256
A5C8BFC67618FB5345AD072E07237271390068B0883C12B04D4B0BEE4E379B96.
An independent Python graph6 decoder checked all 1,449,166 recorded induced
subgraphs. A synthetic exhaustive-permutation oracle cross-check also passes.

**cover9_complement.tsv** is the exact edge-complement list. Its independent
full replay also has zero holes, with incidence SHA-256
D2B2330FBDE43AD96C5435C9F0AC8DF4B444813C694E7A69C5A226684E9FDD0B.
This keeps the raw, DIMACS and historical HOL4 colour conventions explicit.

All large catalogues and products live below
S:\CodexResearchCache\ramsey-formal. The repository keeps only source,
tests and small reports. Set these environment variables to enable the full
tests:

    R45_R44_SOURCE_DIR
    R45_R44_SCANNER
    R45_R44_COVER9_INCIDENCE
    R45_R44_COVER9_WITNESS
    R45_R44_COVER9_COMPLEMENT_INCIDENCE
    R45_R44_CROSSCHECK_DIR

Then run:

    python -B -m unittest discover -s scripts\r45_d12_structural_cover -t . -p test_*.py

For the motif table, frozen source hashes, certificate formats, exact commands,
historical comparison, colour audit and scientific limits, see
../../docs/R45_D12_STRUCTURAL_COVER9_2026-08-07.md and COVER9_MANIFEST.json.

This is a catalogue-relative structural certificate. It does not close any
R(4,5,25) SAT/gluing leaf, does not prove catalogue completeness internally,
and is not a proof of R(4,5) <= 25. The nine motifs were found independently;
a limited indexed-source audit found no prior match, but that audit remains
incomplete.
