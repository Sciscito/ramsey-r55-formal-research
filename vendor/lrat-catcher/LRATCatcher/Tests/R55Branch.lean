import LRATCatcher.Reflect

/-!
  First certified leaf of the R(5,5,43) search.

  This imports the exact standalone DIMACS formula for the branch
  d=20, c=10, catalogue type 0, strengthened by the sound choice of the
  anchor as a minimum-degree vertex of the root neighbourhood.

  `lrat_reflect` checks the external DIMACS parser and LRAT replay inside
  Lean.  Connecting this leaf to the final Ramsey theorem additionally
  requires the formally proved branch-cover and encoding-completeness lemmas.
-/

namespace LRATCatcher.Tests

lrat_reflect r55_d20_c10_t0_min_unsat
  "../../r55/min_d20_c10.cnf"
  "../../r55/min_d20_c10_t0.lrat"

#print axioms r55_d20_c10_t0_min_unsat

-- Hard exceptional W5 formula after 10-regularity and symmetry breaks.
-- This certifies the external strengthened CNF.  Its WLOG connection to the
-- unlabelled Ramsey branch is a separate semantic theorem obligation.
lrat_reflect r55_d20_c10_t312_w5_unsat
  "../../r55/hard_d20_c10_t312_reglex_w5.cnf"
  "../../r55/hard_t312_reglex_w5.lrat"

#print axioms r55_d20_c10_t312_w5_unsat

end LRATCatcher.Tests
