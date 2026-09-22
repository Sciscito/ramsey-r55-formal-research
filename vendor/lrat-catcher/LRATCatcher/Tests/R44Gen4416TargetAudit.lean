import LRATCatcher.Tests.R44RootedGen4416Cover
import LRATCatcher.Tests.R44RootedGraphReduction

/-!
  # Intrinsic `R(4,4)` audit of the two `gen4416` targets

  The rooted classifier cover identifies every allowed row with one of two
  materialized graphs.  This module checks, independently of that cover, that
  both materialized targets are themselves well-formed order-sixteen graphs
  with neither a clique nor an independent set of size four.
-/

namespace LRATCatcher.Tests.R44Gen4416TargetAudit

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R44RootedR34Catalogue
open LRATCatcher.Tests.R44RootedGraphReduction
open LRATCatcher.Tests.R44RootedGen4416Cover
open LRATCatcher.Tests.R44RootedGen4416CoverData

/-! ## Executable clique-four exclusion -/

/-- Executable check excluding cliques of size four. -/
def noCliqueFour (graph : Graph) : Bool :=
  (subsets graph.length 4).all fun vertices =>
    !(pairwise (edge graph) vertices)

/-- The executable clique-four check implies its semantic counterpart. -/
theorem noCliqueFour_semantic
    {graph : Graph} (hcheck : noCliqueFour graph = true) :
    NoCliqueFourAt graph.length graph := by
  unfold noCliqueFour at hcheck
  intro vertices hlength hbound hnodup hclique
  obtain ⟨canonical, hcanonical, hmembership⟩ :=
    subsets_complete graph.length 4 vertices hnodup hbound hlength
  obtain ⟨_, _, hcanonicalNodup⟩ :=
    subsets_valid graph.length 4 canonical hcanonical
  have hcanonicalClique :
      AllDistinctRelated (edge graph) canonical := by
    intro left hleft right hright hne
    exact hclique left ((hmembership left).mp hleft)
      right ((hmembership right).mp hright) hne
  have hpairwise :=
    pairwise_of_allDistinctRelated hcanonicalNodup hcanonicalClique
  have hforbidden := List.all_eq_true.mp hcheck canonical hcanonical
  change (!(pairwise (edge graph) canonical)) = true at hforbidden
  rw [hpairwise] at hforbidden
  contradiction

/-! ## Finite audit of the materialized targets -/

/-- One executable row of the target audit. -/
def checkGen4416TargetR44 (targetIndex : Nat) : Bool :=
  let graph := gen4416Graph targetIndex
  wellFormedGraph 16 graph &&
    noCliqueFour graph &&
    noIndependentFour graph

/-- Audit every materialized target, while also pinning the expected count. -/
def checkAllGen4416TargetsR44 : Bool :=
  gen4416GraphIds.length == 2 &&
    (List.range gen4416GraphIds.length).all checkGen4416TargetR44

theorem gen4416_targets_r44_checked :
    checkAllGen4416TargetsR44 = true := by
  native_decide

/-- Every in-range materialized `gen4416` target satisfies the full semantic
`R(4,4)` graph predicate at order sixteen. -/
theorem gen4416Graph_r44_validAt (targetIndex : Nat)
    (htarget : targetIndex < gen4416GraphIds.length) :
    R44GraphValidAt 16 (gen4416Graph targetIndex) := by
  have hall := gen4416_targets_r44_checked
  unfold checkAllGen4416TargetsR44 at hall
  rw [Bool.and_eq_true] at hall
  have htargetCheck := List.all_eq_true.mp hall.2 targetIndex
    (List.mem_range.mpr htarget)
  unfold checkGen4416TargetR44 at htargetCheck
  simp only [Bool.and_eq_true] at htargetCheck
  have hwellFormed :
      wellFormedGraph 16 (gen4416Graph targetIndex) = true :=
    htargetCheck.1.1
  have hlength : (gen4416Graph targetIndex).length = 16 :=
    wellFormedGraph_length (gen4416Graph targetIndex) 16 hwellFormed
  have hnoClique : NoCliqueFourAt 16 (gen4416Graph targetIndex) := by
    have hsemantic := noCliqueFour_semantic htargetCheck.1.2
    simpa only [hlength] using hsemantic
  have hnoIndependent :
      NoIndependentFourAt 16 (gen4416Graph targetIndex) := by
    have hsemantic := noIndependentFour_semantic htargetCheck.2
    simpa only [hlength] using hsemantic
  exact ⟨hwellFormed, hnoClique, hnoIndependent⟩

#print axioms noCliqueFour_semantic
#print axioms gen4416_targets_r44_checked
#print axioms gen4416Graph_r44_validAt

end LRATCatcher.Tests.R44Gen4416TargetAudit
