import LRATCatcher.Tests.R45RootDegreeCore

/-!
  # Semantic bridge for the red-degree-twelve branch

  An exact red degree of twelve splits the 24 non-root vertices into two
  equal blocks.  The red block is classified by the complete order-12
  `R(3,5)` catalogue (exactly twelve representatives), while the complemented
  blue block is a concrete `(4,4,12)`-free coloring.
-/

namespace LRATCatcher.Tests.R45DegreeTwelveBridge

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R45DegreeReduction
open LRATCatcher.Tests.R45RootDegreeCore

/-- The local finite decoder round-trips at order twelve. -/
theorem localEdgePair_edgeVar_twelve (left right : Fin 12)
    (hordered : left < right) :
    localEdgePair 12 (edgeVar 12 left.val right.val) = (left, right) := by
  native_decide +revert

/-! ## Exact cardinalities and concrete local objects -/

theorem blueDegreeTwelve_length (coloring : Nat → Bool)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    (colorNeighbors coloring root true).length = 12 := by
  exact blueNeighbors_length coloring root hroot (by omega) hdegree

abbrev redDegreeTwelveEmbedding (coloring : Nat → Bool) (root : Nat)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    Fin 12 → AmbientVertex :=
  redNeighborEmbedding 12 coloring root hdegree

abbrev redDegreeTwelveColoring (coloring : Nat → Bool) (root : Nat)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    Nat → Bool :=
  redNeighborColoring 12 coloring root hdegree

abbrev redDegreeTwelveGraph (coloring : Nat → Bool) (root : Nat)
    (hdegree : (colorNeighbors coloring root false).length = 12) : Graph :=
  redNeighborGraph 12 coloring root hdegree

abbrev blueDegreeTwelveEmbedding (coloring : Nat → Bool) (root : Nat)
    (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    Fin 12 → AmbientVertex :=
  blueNeighborEmbedding 12 12 coloring root hroot (by omega) hdegree

abbrev blueDegreeTwelveRawColoring (coloring : Nat → Bool) (root : Nat)
    (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    Nat → Bool :=
  blueNeighborRawColoring 12 12 coloring root hroot (by omega) hdegree

abbrev blueDegreeTwelveColoring (coloring : Nat → Bool) (root : Nat)
    (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    Nat → Bool :=
  blueNeighborColoring 12 12 coloring root hroot (by omega) hdegree

theorem redDegreeTwelveEmbedding_injective (coloring : Nat → Bool)
    (root : Nat)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    Function.Injective (redDegreeTwelveEmbedding coloring root hdegree) := by
  exact redNeighborEmbedding_injective 12 coloring root hdegree

theorem blueDegreeTwelveEmbedding_injective (coloring : Nat → Bool)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    Function.Injective
      (blueDegreeTwelveEmbedding coloring root hroot hdegree) := by
  exact blueNeighborEmbedding_injective 12 12 coloring root hroot
    (by omega) hdegree

/-! ## Canonical `12 + 12` embedding of all non-root vertices -/

/-- Put the red neighbours at local labels `0, ..., 11` and the blue
neighbours at local labels `12, ..., 23`. -/
def degreeTwelveNonRootEmbedding (coloring : Nat → Bool) (root : Nat)
    (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    Fin 24 → AmbientVertex := fun index =>
  if hred : index.val < 12 then
    redDegreeTwelveEmbedding coloring root hdegree ⟨index.val, hred⟩
  else
    blueDegreeTwelveEmbedding coloring root hroot hdegree
      ⟨index.val - 12, by omega⟩

@[simp] theorem degreeTwelveNonRootEmbedding_red
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12)
    (index : Fin 12) :
    degreeTwelveNonRootEmbedding coloring root hroot hdegree
      ⟨index.val, by omega⟩ =
        redDegreeTwelveEmbedding coloring root hdegree index := by
  simp [degreeTwelveNonRootEmbedding]

@[simp] theorem degreeTwelveNonRootEmbedding_blue
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12)
    (index : Fin 12) :
    degreeTwelveNonRootEmbedding coloring root hroot hdegree
      ⟨index.val + 12, by omega⟩ =
        blueDegreeTwelveEmbedding coloring root hroot hdegree index := by
  have hnot : Not (index.val + 12 < 12) := by omega
  simp [degreeTwelveNonRootEmbedding, hnot]

theorem degreeTwelveNonRootEmbedding_ne_root
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12)
    (index : Fin 24) :
    root ≠
      (degreeTwelveNonRootEmbedding coloring root hroot hdegree index).val := by
  by_cases hred : index.val < 12
  · simpa [degreeTwelveNonRootEmbedding, hred] using
      redNeighborEmbedding_ne_root 12 coloring root hdegree
        ⟨index.val, hred⟩
  · simpa [degreeTwelveNonRootEmbedding, hred] using
      blueNeighborEmbedding_ne_root 12 12 coloring root hroot
        (by omega) hdegree ⟨index.val - 12, by omega⟩

/-- The canonical `12 + 12` local layout is an injection into the 25
ambient vertices.  The mixed cases are separated by their root-edge color. -/
theorem degreeTwelveNonRootEmbedding_injective
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    Function.Injective
      (degreeTwelveNonRootEmbedding coloring root hroot hdegree) := by
  intro left right hequal
  by_cases hleft : left.val < 12
  · by_cases hright : right.val < 12
    · have hlocal : (⟨left.val, hleft⟩ : Fin 12) =
          ⟨right.val, hright⟩ := by
        apply redDegreeTwelveEmbedding_injective coloring root hdegree
        simpa [degreeTwelveNonRootEmbedding, hleft, hright] using hequal
      apply Fin.ext
      have hvalues := congrArg (fun index : Fin 12 => index.val) hlocal
      exact hvalues
    · have hredColor := redNeighborEmbedding_color 12 coloring root
          hdegree ⟨left.val, hleft⟩
      have hblueColor := blueNeighborEmbedding_color 12 12 coloring root
          hroot (by omega) hdegree ⟨right.val - 12, by omega⟩
      have hvertices :
          redDegreeTwelveEmbedding coloring root hdegree
              ⟨left.val, hleft⟩ =
            blueDegreeTwelveEmbedding coloring root hroot hdegree
              ⟨right.val - 12, by omega⟩ := by
        simpa [degreeTwelveNonRootEmbedding, hleft, hright] using hequal
      have hvalues := congrArg Fin.val hvertices
      rw [hvalues, hblueColor] at hredColor
      simp at hredColor
  · by_cases hright : right.val < 12
    · have hblueColor := blueNeighborEmbedding_color 12 12 coloring root
          hroot (by omega) hdegree ⟨left.val - 12, by omega⟩
      have hredColor := redNeighborEmbedding_color 12 coloring root
          hdegree ⟨right.val, hright⟩
      have hvertices :
          blueDegreeTwelveEmbedding coloring root hroot hdegree
              ⟨left.val - 12, by omega⟩ =
            redDegreeTwelveEmbedding coloring root hdegree
              ⟨right.val, hright⟩ := by
        simpa [degreeTwelveNonRootEmbedding, hleft, hright] using hequal
      have hvalues := congrArg Fin.val hvertices
      rw [hvalues, hredColor] at hblueColor
      simp at hblueColor
    · have hlocal : (⟨left.val - 12, by omega⟩ : Fin 12) =
          ⟨right.val - 12, by omega⟩ := by
        apply blueDegreeTwelveEmbedding_injective coloring root hroot hdegree
        simpa [degreeTwelveNonRootEmbedding, hleft, hright] using hequal
      have hvalues := congrArg (fun index : Fin 12 => index.val) hlocal
      change left.val - 12 = right.val - 12 at hvalues
      apply Fin.ext
      omega
/-! ## Inherited Ramsey conditions -/

theorem redDegreeTwelveColoring_isRamseyFree
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    isRamseyFree 12 3 5
      (redDegreeTwelveColoring coloring root hdegree) := by
  exact redNeighborColoring_isRamseyFree hfree
    localEdgePair_edgeVar_twelve root hroot hdegree

theorem redDegreeTwelveGraph_validAt
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    GraphValidAt 12 (redDegreeTwelveGraph coloring root hdegree) := by
  exact redNeighborGraph_validAt hfree localEdgePair_edgeVar_twelve
    root hroot hdegree

theorem blueDegreeTwelveColoring_isRamseyFree
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    isRamseyFree 12 4 4
      (blueDegreeTwelveColoring coloring root hroot hdegree) := by
  exact blueNeighborColoring_isRamseyFree hfree
    localEdgePair_edgeVar_twelve root hroot (by omega) hdegree

theorem blueDegreeTwelveRaw_eq_not_complemented
    (coloring : Nat → Bool) (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12)
    (left right : Fin 12) (hordered : left < right) :
    blueDegreeTwelveRawColoring coloring root hroot hdegree
        (edgeVar 12 left.val right.val) =
      !(blueDegreeTwelveColoring coloring root hroot hdegree
        (edgeVar 12 left.val right.val)) := by
  exact blueNeighborRaw_eq_not_complemented coloring root hroot (by omega)
    hdegree localEdgePair_edgeVar_twelve left right hordered

/-! ## Classification by the twelve order-12 `R(3,5)` types -/

theorem r35_catalogue_order_twelve_complete :
    StrongCatalogueComplete 12 (catalogues.getD 12 []) := by
  apply r35_catalogues_complete 12
  rw [extensionWitnesses_length_eq_fourteen]
  omega

theorem r35_catalogue_order_twelve_length :
    (catalogues.getD 12 []).length = 12 := by
  native_decide

/-- Member-oriented form of the order-12 classification. -/
theorem red_degree_twelve_enters_r35_catalogue
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    ∃ representative,
      representative ∈ catalogues.getD 12 [] ∧
      GraphIsomorphicFin
        (redDegreeTwelveGraph coloring root hdegree) representative := by
  exact r35_catalogue_order_twelve_complete
    (redDegreeTwelveGraph coloring root hdegree)
    (redDegreeTwelveGraph_validAt hfree root hroot hdegree)

/-- Indexed form: every exact degree-twelve red block is one of precisely
the twelve certified catalogue types. -/
theorem red_degree_twelve_enters_one_of_twelve_types
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    ∃ typeIndex, typeIndex < 12 ∧
      GraphIsomorphicFin
        (redDegreeTwelveGraph coloring root hdegree)
        ((catalogues.getD 12 []).getD typeIndex []) := by
  obtain ⟨representative, hmember, hisomorphic⟩ :=
    red_degree_twelve_enters_r35_catalogue hfree root hroot hdegree
  obtain ⟨typeIndex, htypeIndex, hget⟩ := List.getElem_of_mem hmember
  have hgetD :
      (catalogues.getD 12 []).getD typeIndex [] = representative := by
    rw [← List.getElem_eq_getD (l := catalogues.getD 12 [])
      (i := typeIndex) (h := htypeIndex) []]
    exact hget
  refine ⟨typeIndex, ?_, ?_⟩
  · simpa [r35_catalogue_order_twelve_length] using htypeIndex
  · rwa [hgetD]

/-- Complete semantic split for the exact red-degree-twelve branch. -/
theorem degree_twelve_local_split
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 25 4 5 coloring)
    (root : Nat) (hroot : root < 25)
    (hdegree : (colorNeighbors coloring root false).length = 12) :
    (∃ typeIndex, typeIndex < 12 ∧
      GraphIsomorphicFin
        (redDegreeTwelveGraph coloring root hdegree)
        ((catalogues.getD 12 []).getD typeIndex [])) ∧
      isRamseyFree 12 4 4
        (blueDegreeTwelveColoring coloring root hroot hdegree) := by
  exact ⟨red_degree_twelve_enters_one_of_twelve_types
      hfree root hroot hdegree,
    blueDegreeTwelveColoring_isRamseyFree hfree root hroot hdegree⟩

#print axioms r35_catalogue_order_twelve_complete
#print axioms degreeTwelveNonRootEmbedding_injective
#print axioms red_degree_twelve_enters_one_of_twelve_types
#print axioms degree_twelve_local_split

end LRATCatcher.Tests.R45DegreeTwelveBridge
