import LRATCatcher.Tests.R35UpperBound
import LRATCatcher.Tests.R35CatalogGraphIsoBridge

/-!
  Integration checkpoint for the complete R(3,5,n) catalogue development.
  Importing this module checks that the semantic completeness chain, the
  closed upper bound R(3,5) ≤ 14, and the auxiliary list-permutation bridge
  coexist in one Lean environment.
-/

namespace LRATCatcher.Tests.R35

#check r35_catalogue_extensions_checked
#check r35_catalogues_complete
#check r35_catalogue_order_ten_complete
#check r35_catalogue_order_fourteen_complete
#check no_graph_valid_at_fourteen
#check r35_upper_catalogue

end LRATCatcher.Tests.R35
