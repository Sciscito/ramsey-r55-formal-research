import LRATCatcher.Reflect

namespace LRATCatcher.Tests.Master8CoreReplay

-- The dependency-traced and densely remapped LRAT replays on the exact
-- ordered-subsequence core CNF.
lrat_reflect master8_core_remapped_unsat
  "../../scripts/r45_d12_cover9_universal/master8_core/cover6_closed_master_d8_bounded13_core.cnf"
  "../../scripts/r45_d12_cover9_universal/master8_core/cover6_closed_master_d8_bounded13_core.lrat"

-- CaDiCaL's independently regenerated LRAT for the same core CNF.  Its
-- generation run used CaDiCaL's internal LRAT checking, and this declaration
-- additionally replays the resulting certificate in LRATCatcher.
lrat_reflect master8_core_cadical_regenerated_unsat
  "../../scripts/r45_d12_cover9_universal/master8_core/cover6_closed_master_d8_bounded13_core.cnf"
  "../../scripts/r45_d12_cover9_universal/master8_core/cadical_regenerated_checked.lrat"

#print axioms master8_core_remapped_unsat
#print axioms master8_core_cadical_regenerated_unsat

end LRATCatcher.Tests.Master8CoreReplay
