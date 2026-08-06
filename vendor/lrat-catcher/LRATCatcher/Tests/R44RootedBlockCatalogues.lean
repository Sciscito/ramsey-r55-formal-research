import LRATCatcher.Tests.R44RootedDegreeSplit
import LRATCatcher.Tests.R44RootedR34Catalogue

/-!
  # Catalogue reduction for the two rooted blocks of an `R(4,4,16)` graph

  Once the root degree split has been oriented, its true-neighbour block has
  order seven and its false-neighbour block has order eight.  This module
  gives both lists their canonical increasing labels, complements the graph
  on the false-neighbour block, proves that the resulting packed graphs are
  `R(3,4)`-valid, and applies the two certified finite catalogues.

  The resulting `GraphIsoFin` witnesses retain their actual finite
  permutations.  They can therefore be assembled later into the global
  order-sixteen relabeling; this file does not perform that assembly.
-/

namespace LRATCatcher.Tests.R44RootedBlockCatalogues

open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R55DegreeBounds
open LRATCatcher.Tests.R44RootedGraphReduction
open LRATCatcher.Tests.R44RootedR34Catalogue
open LRATCatcher.Tests.R44RootedDegreeSplit

/-! ## Generic finite restriction machinery -/

/-- Upper-triangle pairs in the row-major order used by `edgeVar`. -/
def localEdgePairs (order : Nat) : List (Fin order × Fin order) :=
  (List.finRange order).flatMap fun left =>
    (List.finRange order).filterMap fun right =>
      if left < right then some (left, right) else none

/-- Total decoder for local edge-variable indices. -/
def localEdgePair (order index : Nat) [NeZero order] : Fin order × Fin order :=
  (localEdgePairs order).getD index (0, 0)

theorem localEdgePair_edgeVar_seven (left right : Fin 7)
    (hordered : left < right) :
    localEdgePair 7 (edgeVar 7 left.val right.val) = (left, right) := by
  native_decide +revert

theorem localEdgePair_edgeVar_eight (left right : Fin 8)
    (hordered : left < right) :
    localEdgePair 8 (edgeVar 8 left.val right.val) = (left, right) := by
  native_decide +revert

/-- Pull an ambient coloring back along a finite embedding, optionally
complementing every local edge. -/
def restrictedColoring {order : Nat} [NeZero order]
    (embedding : Fin order → Fin 16) (coloring : Nat → Bool)
    (complement : Bool) (index : Nat) : Bool :=
  let endpoints := localEdgePair order index
  let ambient := ramseyEdge 16 coloring
    (embedding endpoints.1).val (embedding endpoints.2).val
  if complement then !ambient else ambient

theorem restrictedColoring_edgeVar
    {order : Nat} [NeZero order]
    (embedding : Fin order → Fin 16) (coloring : Nat → Bool)
    (complement : Bool)
    (hdecoder : ∀ left right : Fin order, left < right →
      localEdgePair order (edgeVar order left.val right.val) = (left, right))
    (left right : Fin order) (hordered : left < right) :
    restrictedColoring embedding coloring complement
        (edgeVar order left.val right.val) =
      if complement then
        !(ramseyEdge 16 coloring (embedding left).val (embedding right).val)
      else
        ramseyEdge 16 coloring (embedding left).val (embedding right).val := by
  simp [restrictedColoring, hdecoder left right hordered]

theorem ramseyEdge_restrictedColoring
    {order : Nat} [NeZero order]
    (embedding : Fin order → Fin 16) (coloring : Nat → Bool)
    (complement : Bool)
    (hdecoder : ∀ left right : Fin order, left < right →
      localEdgePair order (edgeVar order left.val right.val) = (left, right))
    (left right : Fin order) (hne : left ≠ right) :
    ramseyEdge order (restrictedColoring embedding coloring complement)
        left.val right.val =
      if complement then
        !(ramseyEdge 16 coloring (embedding left).val (embedding right).val)
      else
        ramseyEdge 16 coloring (embedding left).val (embedding right).val := by
  rcases Nat.lt_trichotomy left.val right.val with hordered | hequal | hreverse
  · simpa [ramseyEdge, hordered] using
      restrictedColoring_edgeVar embedding coloring complement hdecoder
        left right hordered
  · exact absurd (Fin.ext hequal) hne
  · have hreverseFin : right < left := hreverse
    rw [ramseyEdge_comm order
      (restrictedColoring embedding coloring complement)]
    rw [ramseyEdge_comm 16 coloring]
    simpa [ramseyEdge, hreverse] using
      restrictedColoring_edgeVar embedding coloring complement hdecoder
        right left hreverseFin

/-- Extend a finite embedding to an injective map on naturals. -/
def embedNat {order : Nat} (embedding : Fin order → Fin 16)
    (vertex : Nat) : Nat :=
  if hvertex : vertex < order then
    (embedding ⟨vertex, hvertex⟩).val
  else
    16 + vertex

@[simp] theorem embedNat_of_lt {order : Nat}
    (embedding : Fin order → Fin 16) {vertex : Nat} (hvertex : vertex < order) :
    embedNat embedding vertex = (embedding ⟨vertex, hvertex⟩).val := by
  simp [embedNat, hvertex]

theorem embedNat_bound {order : Nat}
    (embedding : Fin order → Fin 16) {vertex : Nat} (hvertex : vertex < order) :
    embedNat embedding vertex < 16 := by
  rw [embedNat_of_lt embedding hvertex]
  exact (embedding ⟨vertex, hvertex⟩).isLt

theorem embedNat_injective {order : Nat}
    (embedding : Fin order → Fin 16)
    (hinjective : Function.Injective embedding) :
    Function.Injective (embedNat embedding) := by
  intro left right hequal
  by_cases hleft : left < order
  · by_cases hright : right < order
    · have hfin : embedding ⟨left, hleft⟩ = embedding ⟨right, hright⟩ := by
        apply Fin.ext
        simpa [embedNat, hleft, hright] using hequal
      exact congrArg Fin.val (hinjective hfin)
    · have hleftBound := embedNat_bound embedding hleft
      have hrightValue : embedNat embedding right = 16 + right := by
        simp [embedNat, hright]
      omega
  · by_cases hright : right < order
    · have hleftValue : embedNat embedding left = 16 + left := by
        simp [embedNat, hleft]
      have hrightBound := embedNat_bound embedding hright
      omega
    · simpa [embedNat, hleft, hright] using hequal

theorem mapped_nodup {order : Nat}
    (embedding : Fin order → Fin 16)
    (hinjective : Function.Injective embedding)
    {vertices : List Nat} (hnodup : vertices.Nodup) :
    (vertices.map (embedNat embedding)).Nodup := by
  exact hnodup.map (embedNat embedding)
    (fun left right hne hequal =>
      hne (embedNat_injective embedding hinjective hequal))

theorem mapped_bound {order : Nat}
    (embedding : Fin order → Fin 16) {vertices : List Nat}
    (hbound : ∀ vertex, vertex ∈ vertices → vertex < order) :
    ∀ vertex, vertex ∈ vertices.map (embedNat embedding) → vertex < 16 := by
  intro vertex hvertex
  obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
  exact embedNat_bound embedding (hbound index hindex)

theorem local_true_related
    {order : Nat} [NeZero order]
    (embedding : Fin order → Fin 16) (coloring : Nat → Bool)
    (complement : Bool) {vertices : List Nat}
    (hall : ∀ left right,
      left ∈ vertices → right ∈ vertices → left < right →
      restrictedColoring embedding coloring complement
        (edgeVar order left right) = true) :
    LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated
      (ramseyEdge order (restrictedColoring embedding coloring complement))
      vertices := by
  intro left hleft right hright hne
  rcases Nat.lt_or_gt_of_ne hne with hordered | hreverse
  · simpa [ramseyEdge, hordered] using
      hall left right hleft hright hordered
  · rw [ramseyEdge_comm]
    simpa [ramseyEdge, hreverse] using
      hall right left hright hleft hreverse

theorem local_false_related
    {order : Nat} [NeZero order]
    (embedding : Fin order → Fin 16) (coloring : Nat → Bool)
    (complement : Bool) {vertices : List Nat}
    (hall : ∀ left right,
      left ∈ vertices → right ∈ vertices → left < right →
      restrictedColoring embedding coloring complement
        (edgeVar order left right) = false) :
    LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated
      (fun left right =>
        !(ramseyEdge order (restrictedColoring embedding coloring complement)
          left right)) vertices := by
  intro left hleft right hright hne
  rcases Nat.lt_or_gt_of_ne hne with hordered | hreverse
  · have hedge := hall left right hleft hright hordered
    simp [ramseyEdge, hordered, hedge]
  · change Bool.not
      (ramseyEdge order (restrictedColoring embedding coloring complement)
        left right) = true
    rw [ramseyEdge_comm order
      (restrictedColoring embedding coloring complement)]
    have hedge := hall right left hright hleft hreverse
    simp [ramseyEdge, hreverse, hedge]

theorem mapped_true_related
    {order : Nat} [NeZero order]
    (embedding : Fin order → Fin 16) (coloring : Nat → Bool)
    (complement : Bool)
    (hdecoder : ∀ left right : Fin order, left < right →
      localEdgePair order (edgeVar order left.val right.val) = (left, right))
    {vertices : List Nat}
    (hbound : ∀ vertex, vertex ∈ vertices → vertex < order)
    (hrelated : LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated
      (ramseyEdge order (restrictedColoring embedding coloring complement))
      vertices) :
    LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated
      (fun left right =>
        if complement then !(ramseyEdge 16 coloring left right)
        else ramseyEdge 16 coloring left right)
      (vertices.map (embedNat embedding)) := by
  intro left hleft right hright hne
  obtain ⟨indexLeft, hindexLeft, rfl⟩ := List.mem_map.mp hleft
  obtain ⟨indexRight, hindexRight, rfl⟩ := List.mem_map.mp hright
  have hleftBound := hbound indexLeft hindexLeft
  have hrightBound := hbound indexRight hindexRight
  have hindexNe : indexLeft ≠ indexRight := by
    intro hequal
    exact hne (congrArg (embedNat embedding) hequal)
  have hlocal := hrelated indexLeft hindexLeft indexRight hindexRight hindexNe
  have hedge := ramseyEdge_restrictedColoring embedding coloring complement
    hdecoder ⟨indexLeft, hleftBound⟩ ⟨indexRight, hrightBound⟩ (by
      intro hequal
      exact hindexNe (congrArg Fin.val hequal))
  rw [embedNat_of_lt embedding hleftBound,
    embedNat_of_lt embedding hrightBound]
  rw [hedge] at hlocal
  simpa using hlocal

theorem mapped_false_related
    {order : Nat} [NeZero order]
    (embedding : Fin order → Fin 16) (coloring : Nat → Bool)
    (complement : Bool)
    (hdecoder : ∀ left right : Fin order, left < right →
      localEdgePair order (edgeVar order left.val right.val) = (left, right))
    {vertices : List Nat}
    (hbound : ∀ vertex, vertex ∈ vertices → vertex < order)
    (hrelated : LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated
      (fun left right =>
        !(ramseyEdge order (restrictedColoring embedding coloring complement)
          left right)) vertices) :
    LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated
      (fun left right =>
        !(if complement then !(ramseyEdge 16 coloring left right)
          else ramseyEdge 16 coloring left right))
      (vertices.map (embedNat embedding)) := by
  intro left hleft right hright hne
  obtain ⟨indexLeft, hindexLeft, rfl⟩ := List.mem_map.mp hleft
  obtain ⟨indexRight, hindexRight, rfl⟩ := List.mem_map.mp hright
  have hleftBound := hbound indexLeft hindexLeft
  have hrightBound := hbound indexRight hindexRight
  have hindexNe : indexLeft ≠ indexRight := by
    intro hequal
    exact hne (congrArg (embedNat embedding) hequal)
  have hlocal := hrelated indexLeft hindexLeft indexRight hindexRight hindexNe
  have hedge := ramseyEdge_restrictedColoring embedding coloring complement
    hdecoder ⟨indexLeft, hleftBound⟩ ⟨indexRight, hrightBound⟩ (by
      intro hequal
      exact hindexNe (congrArg Fin.val hequal))
  rw [embedNat_of_lt embedding hleftBound,
    embedNat_of_lt embedding hrightBound]
  change Bool.not
    (ramseyEdge order (restrictedColoring embedding coloring complement)
      indexLeft indexRight) = true at hlocal
  rw [hedge] at hlocal
  simpa using hlocal

/-! ## A same-colour neighbourhood inherits an `R(3,4)` coloring -/

theorem neighborhood_restricted_isRamseyFree
    {order : Nat} [NeZero order] {coloring : Nat → Bool}
    (hfree : isRamseyFree 16 4 4 coloring)
    (embedding : Fin order → Fin 16)
    (hinjective : Function.Injective embedding)
    (hdecoder : ∀ left right : Fin order, left < right →
      localEdgePair order (edgeVar order left.val right.val) = (left, right))
    (rootVertex : Fin 16) (complement : Bool)
    (hrootNe : ∀ index, rootVertex.val ≠ (embedding index).val)
    (hneighbour : ∀ index,
      ramseyEdge 16 coloring rootVertex.val (embedding index).val = !complement) :
    isRamseyFree order 3 4
      (restrictedColoring embedding coloring complement) := by
  constructor
  · intro vertices hlength hbound hnodup hall
    let mapped := vertices.map (embedNat embedding)
    let forbidden := rootVertex.val :: mapped
    have hmappedNodup : mapped.Nodup :=
      mapped_nodup embedding hinjective hnodup
    have hmappedBound : ∀ vertex, vertex ∈ mapped → vertex < 16 :=
      mapped_bound embedding hbound
    have hrootNotMapped : rootVertex.val ∉ mapped := by
      intro hmember
      obtain ⟨index, hindex, hequal⟩ := List.mem_map.mp hmember
      have hindexBound := hbound index hindex
      have hequal' : rootVertex.val =
          (embedding ⟨index, hindexBound⟩).val := by
        simpa [embedNat, hindexBound] using hequal.symm
      exact hrootNe ⟨index, hindexBound⟩ hequal'
    have hforbiddenLength : forbidden.length = 4 := by
      simp [forbidden, mapped, hlength]
    have hforbiddenBound :
        ∀ vertex, vertex ∈ forbidden → vertex < 16 := by
      intro vertex hvertex
      simp only [forbidden, List.mem_cons] at hvertex
      rcases hvertex with rfl | hvertex
      · exact rootVertex.isLt
      · exact hmappedBound vertex hvertex
    have hforbiddenNodup : forbidden.Nodup := by
      simp only [forbidden, List.nodup_cons]
      exact ⟨hrootNotMapped, hmappedNodup⟩
    have hlocal := local_true_related embedding coloring complement hall
    have hmapped := mapped_true_related embedding coloring complement
      hdecoder hbound hlocal
    cases complement with
    | false =>
        have hmappedRed :
            LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated (ramseyEdge 16 coloring) mapped := by
          simpa using hmapped
        have hforbiddenRed :
            LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated (ramseyEdge 16 coloring) forbidden := by
          apply allDistinctRelated_cons
          · exact ramseyEdge_comm 16 coloring
          · exact hmappedRed
          · intro vertex hvertex
            obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
            have hindexBound := hbound index hindex
            rw [embedNat_of_lt embedding hindexBound]
            simpa using hneighbour ⟨index, hindexBound⟩
        apply hfree.1 forbidden hforbiddenLength hforbiddenBound
          hforbiddenNodup
        intro left right hleft hright hordered
        have hedge := hforbiddenRed left hleft right hright
          (Nat.ne_of_lt hordered)
        simpa [ramseyEdge, hordered] using hedge
    | true =>
        have hmappedBlue :
            LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated
              (fun left right => !(ramseyEdge 16 coloring left right))
              mapped := by
          simpa using hmapped
        have hforbiddenBlue :
            LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated
              (fun left right => !(ramseyEdge 16 coloring left right))
              forbidden := by
          apply allDistinctRelated_cons
          · intro left right
            rw [ramseyEdge_comm 16 coloring left right]
          · exact hmappedBlue
          · intro vertex hvertex
            obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
            have hindexBound := hbound index hindex
            rw [embedNat_of_lt embedding hindexBound]
            have hedge := hneighbour ⟨index, hindexBound⟩
            simp at hedge ⊢
            exact hedge
        apply hfree.2 forbidden hforbiddenLength hforbiddenBound
          hforbiddenNodup
        intro left right hleft hright hordered
        have hedge := hforbiddenBlue left hleft right hright
          (Nat.ne_of_lt hordered)
        simpa [ramseyEdge, hordered] using hedge
  · intro vertices hlength hbound hnodup hall
    let mapped := vertices.map (embedNat embedding)
    have hmappedNodup : mapped.Nodup :=
      mapped_nodup embedding hinjective hnodup
    have hmappedBound : ∀ vertex, vertex ∈ mapped → vertex < 16 :=
      mapped_bound embedding hbound
    have hlocal := local_false_related embedding coloring complement hall
    have hmapped := mapped_false_related embedding coloring complement
      hdecoder hbound hlocal
    cases complement with
    | false =>
        have hmappedBlue :
            LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated
              (fun left right => !(ramseyEdge 16 coloring left right))
              mapped := by
          simpa using hmapped
        apply hfree.2 mapped (by simp [mapped, hlength]) hmappedBound
          hmappedNodup
        intro left right hleft hright hordered
        have hedge := hmappedBlue left hleft right hright
          (Nat.ne_of_lt hordered)
        simpa [ramseyEdge, hordered] using hedge
    | true =>
        have hmappedRed :
            LRATCatcher.Tests.R55DegreeBounds.AllDistinctRelated (ramseyEdge 16 coloring) mapped := by
          simpa using hmapped
        apply hfree.1 mapped (by simp [mapped, hlength]) hmappedBound
          hmappedNodup
        intro left right hleft hright hordered
        have hedge := hmappedRed left hleft right hright
          (Nat.ne_of_lt hordered)
        simpa [ramseyEdge, hordered] using hedge

/-! ## From local `R(3,4)` colorings to the catalogue predicate -/

theorem coloringGraph_r34_validAt
    (order : Nat) (coloring : Nat → Bool)
    (hfree : isRamseyFree order 3 4 coloring) :
    R34GraphValidAt order (coloringGraph order coloring) := by
  have hwellFormed := coloringGraph_wellFormed order coloring
  have hnoIndependentSemantic :
      NoIndependentFourAt order (coloringGraph order coloring) := by
    intro vertices hlength hbound hnodup hindependent
    apply hfree.2 vertices hlength hbound hnodup
    intro left right hleft hright hordered
    have hleftBound := hbound left hleft
    have hrightBound := hbound right hright
    have hedge := hindependent left hleft right hright
      (Nat.ne_of_lt hordered)
    change Bool.not
      (edge (coloringGraph order coloring) left right) = true at hedge
    rw [edge_coloringGraph order coloring
      ⟨left, hleftBound⟩ ⟨right, hrightBound⟩] at hedge
    simpa [coloringEdge, hordered] using hedge
  have hnoIndependentCheck :
      noIndependentFour (coloringGraph order coloring) = true :=
    semantic_noIndependentFour hwellFormed hnoIndependentSemantic
  have hsemantic :
      SemanticallyValidGraph order (coloringGraph order coloring) := by
    constructor
    · intro vertices hlength hbound hnodup htriangle
      apply hfree.1 vertices hlength hbound hnodup
      intro left right hleft hright hordered
      have hleftBound := hbound left hleft
      have hrightBound := hbound right hright
      have hedge := htriangle left hleft right hright
        (Nat.ne_of_lt hordered)
      rw [edge_coloringGraph order coloring
        ⟨left, hleftBound⟩ ⟨right, hrightBound⟩] at hedge
      simpa [coloringEdge, hordered] using hedge
    · intro vertices hlength hbound hnodup hindependent
      let chosen := vertices.take 4
      have hchosenLength : chosen.length = 4 := by
        simp [chosen, hlength]
      have hchosenBound : ∀ vertex, vertex ∈ chosen → vertex < order := by
        intro vertex hvertex
        exact hbound vertex (List.mem_of_mem_take hvertex)
      have hchosenNodup : chosen.Nodup := by
        simpa [chosen] using hnodup.take
      apply hnoIndependentSemantic chosen hchosenLength hchosenBound
        hchosenNodup
      intro left hleft right hright hne
      exact hindependent left (List.mem_of_mem_take hleft)
        right (List.mem_of_mem_take hright) hne
  exact ⟨⟨hwellFormed, semantic_validGraph hwellFormed hsemantic⟩,
    hnoIndependentCheck⟩

/-! ## Canonically labelled root blocks -/

def leftVertex (coloring : Nat → Bool) (flip : Bool)
    (hlength : (leftBlock coloring flip).length = 7)
    (index : Fin 7) : Fin 16 :=
  ⟨(leftBlock coloring flip)[index.val]'(by simpa [hlength] using index.isLt),
    leftBlock_bound coloring flip (List.getElem_mem _)⟩

def antiVertex (coloring : Nat → Bool) (flip : Bool)
    (hlength : (antiBlock coloring flip).length = 8)
    (index : Fin 8) : Fin 16 :=
  ⟨(antiBlock coloring flip)[index.val]'(by simpa [hlength] using index.isLt),
    antiBlock_bound coloring flip (List.getElem_mem _)⟩

theorem leftVertex_mem (coloring : Nat → Bool) (flip : Bool)
    (hlength : (leftBlock coloring flip).length = 7) (index : Fin 7) :
    (leftVertex coloring flip hlength index).val ∈ leftBlock coloring flip := by
  exact List.getElem_mem _

theorem antiVertex_mem (coloring : Nat → Bool) (flip : Bool)
    (hlength : (antiBlock coloring flip).length = 8) (index : Fin 8) :
    (antiVertex coloring flip hlength index).val ∈ antiBlock coloring flip := by
  exact List.getElem_mem _

@[simp] theorem root_leftVertex_color
    (coloring : Nat → Bool) (flip : Bool)
    (hlength : (leftBlock coloring flip).length = 7) (index : Fin 7) :
    ramseyEdge 16 (orientedColoring coloring flip) root
      (leftVertex coloring flip hlength index).val = true := by
  exact (mem_trueNeighbors _ _).mp
    (leftVertex_mem coloring flip hlength index) |>.2

@[simp] theorem root_antiVertex_color
    (coloring : Nat → Bool) (flip : Bool)
    (hlength : (antiBlock coloring flip).length = 8) (index : Fin 8) :
    ramseyEdge 16 (orientedColoring coloring flip) root
      (antiVertex coloring flip hlength index).val = false := by
  exact (mem_falseNeighbors _ _).mp
    (antiVertex_mem coloring flip hlength index) |>.2

theorem leftVertex_ne_root
    (coloring : Nat → Bool) (flip : Bool)
    (hlength : (leftBlock coloring flip).length = 7) (index : Fin 7) :
    (leftVertex coloring flip hlength index).val ≠ root :=
  trueNeighbors_ne_root _ (leftVertex_mem coloring flip hlength index)

theorem antiVertex_ne_root
    (coloring : Nat → Bool) (flip : Bool)
    (hlength : (antiBlock coloring flip).length = 8) (index : Fin 8) :
    (antiVertex coloring flip hlength index).val ≠ root :=
  falseNeighbors_ne_root _ (antiVertex_mem coloring flip hlength index)
theorem leftVertex_injective (coloring : Nat → Bool) (flip : Bool)
    (hlength : (leftBlock coloring flip).length = 7) :
    Function.Injective (leftVertex coloring flip hlength) := by
  intro left right hequal
  apply Fin.ext
  have hvalues := congrArg Fin.val hequal
  exact (List.getElem_inj (leftBlock_nodup coloring flip)).mp hvalues

theorem antiVertex_injective (coloring : Nat → Bool) (flip : Bool)
    (hlength : (antiBlock coloring flip).length = 8) :
    Function.Injective (antiVertex coloring flip hlength) := by
  intro left right hequal
  apply Fin.ext
  have hvalues := congrArg Fin.val hequal
  exact (List.getElem_inj (antiBlock_nodup coloring flip)).mp hvalues

def leftInducedColoring (coloring : Nat → Bool) (flip : Bool)
    (hlength : (leftBlock coloring flip).length = 7) : Nat → Bool :=
  restrictedColoring (leftVertex coloring flip hlength)
    (orientedColoring coloring flip) false

def antiInducedColoring (coloring : Nat → Bool) (flip : Bool)
    (hlength : (antiBlock coloring flip).length = 8) : Nat → Bool :=
  restrictedColoring (antiVertex coloring flip hlength)
    (orientedColoring coloring flip) true

def leftInducedGraph (coloring : Nat → Bool) (flip : Bool)
    (hlength : (leftBlock coloring flip).length = 7) : Graph :=
  coloringGraph 7 (leftInducedColoring coloring flip hlength)

def antiInducedGraph (coloring : Nat → Bool) (flip : Bool)
    (hlength : (antiBlock coloring flip).length = 8) : Graph :=
  coloringGraph 8 (antiInducedColoring coloring flip hlength)

@[simp] theorem leftInducedGraph_length
    (coloring : Nat → Bool) (flip : Bool)
    (hlength : (leftBlock coloring flip).length = 7) :
    (leftInducedGraph coloring flip hlength).length = 7 := by
  simp [leftInducedGraph]

@[simp] theorem antiInducedGraph_length
    (coloring : Nat → Bool) (flip : Bool)
    (hlength : (antiBlock coloring flip).length = 8) :
    (antiInducedGraph coloring flip hlength).length = 8 := by
  simp [antiInducedGraph]

theorem edge_leftInducedGraph
    (coloring : Nat → Bool) (flip : Bool)
    (hlength : (leftBlock coloring flip).length = 7)
    (left right : Fin 7) (hne : left ≠ right) :
    edge (leftInducedGraph coloring flip hlength) left.val right.val =
      ramseyEdge 16 (orientedColoring coloring flip)
        (leftVertex coloring flip hlength left).val
        (leftVertex coloring flip hlength right).val := by
  rw [leftInducedGraph, edge_coloringGraph]
  change ramseyEdge 7 (leftInducedColoring coloring flip hlength)
      left.val right.val = _
  unfold leftInducedColoring
  simpa using ramseyEdge_restrictedColoring
    (leftVertex coloring flip hlength)
    (orientedColoring coloring flip) false
    localEdgePair_edgeVar_seven left right hne

theorem edge_antiInducedGraph
    (coloring : Nat → Bool) (flip : Bool)
    (hlength : (antiBlock coloring flip).length = 8)
    (left right : Fin 8) (hne : left ≠ right) :
    edge (antiInducedGraph coloring flip hlength) left.val right.val =
      !(ramseyEdge 16 (orientedColoring coloring flip)
        (antiVertex coloring flip hlength left).val
        (antiVertex coloring flip hlength right).val) := by
  rw [antiInducedGraph, edge_coloringGraph]
  change ramseyEdge 8 (antiInducedColoring coloring flip hlength)
      left.val right.val = _
  unfold antiInducedColoring
  simpa using ramseyEdge_restrictedColoring
    (antiVertex coloring flip hlength)
    (orientedColoring coloring flip) true
    localEdgePair_edgeVar_eight left right hne
theorem leftInducedColoring_isRamseyFree
    {coloring : Nat → Bool} {flip : Bool}
    (hfree : isRamseyFree 16 4 4 (orientedColoring coloring flip))
    (hlength : (leftBlock coloring flip).length = 7) :
    isRamseyFree 7 3 4 (leftInducedColoring coloring flip hlength) := by
  apply neighborhood_restricted_isRamseyFree hfree
    (leftVertex coloring flip hlength)
    (leftVertex_injective coloring flip hlength)
    localEdgePair_edgeVar_seven ⟨root, by simp [root]⟩ false
  · intro index
    exact (trueNeighbors_ne_root _
      (leftVertex_mem coloring flip hlength index)).symm
  · intro index
    exact (mem_trueNeighbors _ _).mp
      (leftVertex_mem coloring flip hlength index) |>.2

theorem antiInducedColoring_isRamseyFree
    {coloring : Nat → Bool} {flip : Bool}
    (hfree : isRamseyFree 16 4 4 (orientedColoring coloring flip))
    (hlength : (antiBlock coloring flip).length = 8) :
    isRamseyFree 8 3 4 (antiInducedColoring coloring flip hlength) := by
  apply neighborhood_restricted_isRamseyFree hfree
    (antiVertex coloring flip hlength)
    (antiVertex_injective coloring flip hlength)
    localEdgePair_edgeVar_eight ⟨root, by simp [root]⟩ true
  · intro index
    exact (falseNeighbors_ne_root _
      (antiVertex_mem coloring flip hlength index)).symm
  · intro index
    simpa using (mem_falseNeighbors _ _).mp
      (antiVertex_mem coloring flip hlength index) |>.2

theorem leftInducedGraph_r34_validAt
    {coloring : Nat → Bool} {flip : Bool}
    (hfree : isRamseyFree 16 4 4 (orientedColoring coloring flip))
    (hlength : (leftBlock coloring flip).length = 7) :
    R34GraphValidAt 7 (leftInducedGraph coloring flip hlength) := by
  exact coloringGraph_r34_validAt 7 _
    (leftInducedColoring_isRamseyFree hfree hlength)

theorem antiInducedGraph_r34_validAt
    {coloring : Nat → Bool} {flip : Bool}
    (hfree : isRamseyFree 16 4 4 (orientedColoring coloring flip))
    (hlength : (antiBlock coloring flip).length = 8) :
    R34GraphValidAt 8 (antiInducedGraph coloring flip hlength) := by
  exact coloringGraph_r34_validAt 8 _
    (antiInducedColoring_isRamseyFree hfree hlength)

/-! ## Explicit catalogue indices and strong block isomorphisms -/

set_option maxHeartbeats 0 in
structure RootBlockCatalogueWitness (coloring : Nat → Bool) where
  flip : Bool
  orientedFree : isRamseyFree 16 4 4 (orientedColoring coloring flip)
  leftLength : (leftBlock coloring flip).length = 7
  antiLength : (antiBlock coloring flip).length = 8
  leftIndex : Nat
  leftIndexBound : leftIndex < r34Catalogue7.length
  leftIsomorphism : GraphIsoFin
    (leftInducedGraph coloring flip leftLength)
    (r34Catalogue7.getD leftIndex [])
  antiIndex : Nat
  antiIndexBound : antiIndex < r34Catalogue8.length
  antiIsomorphism : GraphIsoFin
    (antiInducedGraph coloring flip antiLength)
    (r34Catalogue8.getD antiIndex [])

/-- Apply both complete catalogues to an explicitly oriented split. -/
theorem oriented_blocks_enter_catalogues
    {coloring : Nat → Bool} (flip : Bool)
    (hfree : isRamseyFree 16 4 4 (orientedColoring coloring flip))
    (hleft : (leftBlock coloring flip).length = 7)
    (hanti : (antiBlock coloring flip).length = 8) :
    Nonempty (RootBlockCatalogueWitness coloring) := by
  obtain ⟨leftRepresentative, hleftMember, ⟨hleftIso⟩⟩ :=
    r34_catalogue_seven_complete
      (leftInducedGraph coloring flip hleft)
      (leftInducedGraph_r34_validAt hfree hleft)
  obtain ⟨leftIndex, hleftIndex, hleftGet⟩ :=
    List.getElem_of_mem hleftMember
  have hleftGetD : r34Catalogue7.getD leftIndex [] = leftRepresentative := by
    rw [← List.getElem_eq_getD (l := r34Catalogue7) (i := leftIndex)
      (h := hleftIndex) []]
    exact hleftGet
  obtain ⟨antiRepresentative, hantiMember, ⟨hantiIso⟩⟩ :=
    r34_catalogue_eight_complete
      (antiInducedGraph coloring flip hanti)
      (antiInducedGraph_r34_validAt hfree hanti)
  obtain ⟨antiIndex, hantiIndex, hantiGet⟩ :=
    List.getElem_of_mem hantiMember
  have hantiGetD : r34Catalogue8.getD antiIndex [] = antiRepresentative := by
    rw [← List.getElem_eq_getD (l := r34Catalogue8) (i := antiIndex)
      (h := hantiIndex) []]
    exact hantiGet
  exact ⟨{
    flip := flip
    orientedFree := hfree
    leftLength := hleft
    antiLength := hanti
    leftIndex := leftIndex
    leftIndexBound := hleftIndex
    leftIsomorphism := by
      simpa only [hleftGetD] using hleftIso
    antiIndex := antiIndex
    antiIndexBound := hantiIndex
    antiIsomorphism := by
      simpa only [hantiGetD] using hantiIso
  }⟩

/-- Every semantic oriented root split supplies concrete catalogue selectors
and strong block isomorphisms. -/
theorem rooted_blocks_enter_catalogues
    {coloring : Nat → Bool} (split : OrientedRootSplit coloring) :
    Nonempty (RootBlockCatalogueWitness coloring) := by
  obtain ⟨flip, hfree, hleft, hanti⟩ := split
  exact oriented_blocks_enter_catalogues flip hfree hleft hanti

#print axioms leftInducedGraph_r34_validAt
#print axioms antiInducedGraph_r34_validAt
#print axioms rooted_blocks_enter_catalogues

end LRATCatcher.Tests.R44RootedBlockCatalogues
