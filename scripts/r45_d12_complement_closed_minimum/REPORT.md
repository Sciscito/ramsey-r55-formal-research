# Exact complement-closed cover minimum

Date: 2026-08-07. Status: verified computational result.

## Result

The exact minimum is three complement pairs, hence six order-seven motif
classes, for the frozen official `R(4,4,12)` catalogue. There is no cover by
one or two pairs; the three pairs in `cover6_complement_closed.tsv` cover every
one of the 1,449,166 records.

Because an order-seven graph has 21 edges, no order-seven isomorphism class can
be fixed by complementation. Independent reconstruction confirms that the 362
official classes split into exactly 181 two-cycles.

## Lower bound

The standalone verifier does not read the K12 incidence matrix. It:

1. examines all `2^21` labelled order-seven graphs;
2. identifies exactly 923,012 labelled `R(4,4,7)` graphs and the 362 classes;
3. reconstructs all 181 complement pairs by an independent labelled map;
4. directly verifies the 30 records in `kernel30_r44_12.g6` as `R(4,4,12)`;
5. recomputes their 30 × 792 induced order-seven signatures; and
6. excludes all 16,471 choices of at most two complement pairs.

The kernel is deletion-irredundant. Its SHA-256 is
`EB61306B5DA0F15DC1112D82007BB29CD2FD3AEE460FD1C0D62E24401C66C8CC`;
the signature SHA-256 is
`FD92B41FAD600EEC47FA5214EA1F36D9E7B1B6D44DDBE8EADFD029F41EFD89A9`.

## Upper bound

Three independent views agree:

- exact bitset search on the full 362-column incidence matrix gives zero
  uncovered records and pair-removal holes `(22, 446, 40)`;
- a native scanner generated a 1,449,166-entry subset witness, which was
  independently replayed entry by entry; and
- `verify_cover6.py` rebuilt the 25,200 labelled motif copies and scanned the
  official K12 graph6 source directly, without reading incidence or witness.

The direct first-hit distribution is
`(46,679, 347,807, 698,002, 36,774, 108,486, 211,418)`. Explicit removal
witnesses occur at catalogue indices 277,215, 3,927, and 121,102.

## Interpretation and limits

This improves the previously observed eight-class complement closure of the
five-class unconstrained cover. It does not contradict the unconstrained
minimum five: complement closure is an extra condition, and six is even as
required.

The lower bound is absolute on explicit valid graphs. The upper bound depends
on the frozen official exhaustive K12 catalogue and its source hash. The result
does not close any of the twelve order-12 gluing selector cases and is not a
proof of a new value of `R(4,5)` or `R(5,5)`. It appears research-worthy, but
novelty against the full literature has not been established.
