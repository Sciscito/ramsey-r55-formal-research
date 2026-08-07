# Degree-12 two-centre cover experiment

## Status

This directory contains the deterministic source and light tests for a
compressed cover of the `R(4,4,12)` right-neighbour block in the red-degree-12
branch of `R(4,5,25)`.

The result is a useful experimental reduction, not a proof of the full d12
branch.  Its mathematical coverage is conditional on the completeness of the
official Gauthier--Brown/HOL4 `gen4412` child catalogue.  The external
certificate checks every transformation of the 26,845 parent records, but it
does not independently prove that the 1,449,166 children exhaust all
`R(4,4,12)` colourings.

No large generated object is tracked here.  CNFs, manifests, the 7 MB cover
certificate, and LRAT proofs remain on the external SSD.

## Frozen source

Official extracted cover:

```text
S:\CodexResearchCache\ramsey-formal\literature\barakeel-gen\gen\gen4412
```

- SHA-256: `317F7D55DEAB37EC2AA98557F7F483F55281AFF04BFC8E4ECDA1CF2DEEDF0385`
- 26,845 parent records
- 1,449,166 child instances
- 0..8 holes per parent

The independent repository checker
`scripts/r45_d8_pilot/check_barakeel_covers.py` separately checks the file
grammar, encoded order, stored permutations, complete children, uniqueness,
and parent/child agreement.

## Construction and exact coverage

Project each parent onto all 21 edges incident to local vertices 0 or 1.  Each
centre has fixed degree at least three because an original parent has at most
eight holes; every other vertex has projected fixed degree at most two.
Consequently an isomorphism must preserve the unordered pair of centres.

A projected isomorphism class is therefore represented exactly by:

- the colour or hole on edge `(0,1)`;
- the multiset of ten two-entry outside profiles;
- an optional swap of the two centres.

The deterministic counts are:

- 21,468 distinct oriented projections;
- 857 exact isomorphism classes;
- 64 subsumption-minimal weak motifs modulo those isomorphisms.

Every source parent is assigned to the first compatible weak motif.  The
script records a permutation with convention

```text
new_to_old[a] = source vertex placed at canonical vertex a
transformed(a,b) = source(new_to_old[a], new_to_old[b]).
```

For each of the 64 assigned groups, the full 66-edge coordinatewise consensus
retains precisely the non-hole literals shared after these permutations.
Thus:

- the 64 weak motifs cover all 26,845 parents, with overlaps allowed;
- the recorded first-match assignments form a partition of all parents;
- each of the 64 fused motifs covers every parent in its assigned group;
- all 26,845 direct weak implications and all 26,845 fused-consensus
  implications are checked during regeneration.

The fused motifs have 14..59 fixed units, median 35 and mean 37.34375.  The
largest group is the 14-unit motif 1 with 21,182 assigned parents, so the
compression alone does not make every SAT leaf easy.

## Colour and SAT convention

The source convention is HOL colour 1 = blue and colour 2 = red.  The reduced
DIMACS/Lean assignment instead uses Boolean true for red.  This two-centre
pipeline therefore uses the explicit Lean `.rawHOL` transport:

```text
HOL 0 (hole) -> no unit
HOL 1 (blue) -> DIMACS negative / raw B = false
HOL 2 (red)  -> DIMACS positive / raw B = true
```

The tracked `raw_hol_dimacs_units` function performs that conversion after
shifting local B vertices by 12, so its variables are exactly 211 through 276.
This is not the palette-swapped `color1 -> positive` orientation used by the
separate conditioned-core experiment.

## External certificate

The deterministically generated certificate used during this experiment is:

```text
S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-two-center-cover\two_center_consensus_certificate.json
```

- size: 7,047,484 bytes
- SHA-256: `092EB9F45BD0F8761CF139677CBA3B11DB19575B6BFE103C7EB767AD5C388FDA`
- schema: `gen4412-two-centre-consensus-v1`
- patterns: 64
- assignments: 26,845

Generate it only on `S:`:

```powershell
python -B scripts\r45_d12_two_center_cover\generate_certificate.py generate `
  S:\CodexResearchCache\ramsey-formal\literature\barakeel-gen\gen\gen4412 `
  S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-two-center-cover\two_center_consensus_certificate.json
```

Regenerate all invariants without requiring a saved certificate:

```powershell
python -B scripts\r45_d12_two_center_cover\generate_certificate.py verify `
  S:\CodexResearchCache\ramsey-formal\literature\barakeel-gen\gen\gen4412
```

Or compare against the external certificate byte for byte:

```powershell
python -B scripts\r45_d12_two_center_cover\generate_certificate.py verify `
  S:\CodexResearchCache\ramsey-formal\literature\barakeel-gen\gen\gen4412 `
  S:\CodexResearchCache\ramsey-formal\lrat-work\r45-d12-two-center-cover\two_center_consensus_certificate.json
```

## Certified sampled leaf

The SAT experiment called `p64` uses fused motif 64, not merely its weak
17-unit skeleton:

- fused fixed mask: `73786974989168146417`
- fused red mask: `22005668064597575169`
- 59 fixed units: 29 red and 30 blue
- singleton source parent record: 9,973
- `new_to_old = [1,0,2,6,5,11,10,8,4,3,9,7]`

For left catalogue type 1, its sampled CNF was UNSAT in 305,787 conflicts.

- CNF SHA-256: `2A82407F384C3DA3661651738A0D6884844753353BBA7AC4B56CF6FF2E00BD9F`
- LRAT size: 62,911,549 bytes
- LRAT SHA-256: `4556AE3A2BDFFD54FC15BEAB21AD86BD8B475063CE54A75A34BECE22B42F072D`
- solver log SHA-256: `9A2BE466322B684E75737865B244747A21F99D7B0F5B18A33F8BC8C1F6DA7DCC`
- Lean `lrat_reflect` replay: successful

The historical external `fused64-sample1m/manifest.json` predates an explicit
`catalogue_orientation` field and is intentionally left unchanged.  Its 59
stored literals were independently recomputed from the certified masks with
the tracked `.rawHOL` conversion: the sequence matches exactly, uses variables
211..276, and contains 29 positive and 30 negative literals.  The certificate
itself records the same `1 = blue / negative`, `2 = red / positive` convention.

Only this sampled cover leaf is certified UNSAT.  Other tested representatives,
including the dominant 14-unit motif, remained UNKNOWN at one million
conflicts.

## Direct one-centre consequence

There is also a catalogue-independent explanation for the coarser one-centre
projection.  In an `R(4,4)`-free colouring of `K12`, no vertex has nine red
neighbours: `R(3,4) <= 9` would give either a red triangle, forming a red `K4`
with the centre, or a blue `K4`.  The colour-swapped argument bounds blue
degree by eight.  Every vertex therefore has at least three neighbours of each
colour, so six incident right-block units can be fixed WLOG after relabelling.

## Tests

The light suite uses only synthetic patterns.  It checks the SSD output guard,
permutation convention and round trip, wildcard profile matching, direct
orientation, consensus implication, isomorphism-aware subsumption, and the
non-regression polarity `HOL 1 -> -211`, `HOL 2 -> +276`:

```powershell
python -B scripts\r45_d12_two_center_cover\test_generate_certificate.py
```

## Remaining proof obligations

Before this becomes a certified d12 theorem, the project still needs:

1. a Lean-certified completeness bridge for the `R(4,4,12)` catalogue or an
   independently certified replacement;
2. a Lean finite certificate for the two-centre quotient, 64-way subsumption,
   recorded permutations, and consensus implications;
3. transport of the right-block permutations through the full fixed-root CNF
   while preserving the chosen left `R(3,5,12)` type;
4. guarded composition of all `12 x 64 = 768` leaves;
5. UNSAT LRATs and Lean replay for every leaf.

Accordingly, this is a reproducible cover compression plus one certified
sample leaf, not yet a complete or publishable d12 result.
