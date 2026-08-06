import LRATCatcher.Showcases.Ramsey

/-!
  # Degree bounds in a hypothetical `R(5,5,43)` counterexample

  The only external Ramsey input is `R(4,5) ≤ 25`, stated as
  `¬ hasRamseyFreeColoring 25 4 5`.  Restricting a `K₅/K₅`-free coloring
  to 25 neighbours of one colour, and complementing in the blue case,
  would produce a forbidden `K₂₅` coloring with no red `K₄` and no blue
  `K₅`.  Hence every red and every blue degree is at most 24.
-/

namespace LRATCatcher.Tests.R55DegreeBounds

open LRATCatcher.Ramsey

/-- Symmetric, loop-free view of an upper-triangle Ramsey coloring. -/
def ramseyEdge (order : Nat) (coloring : Nat → Bool)
    (left right : Nat) : Bool :=
  if left < right then
    coloring (edgeVar order left right)
  else if right < left then
    coloring (edgeVar order right left)
  else
    false

@[simp] theorem ramseyEdge_self (order : Nat) (coloring : Nat → Bool)
    (vertex : Nat) :
    ramseyEdge order coloring vertex vertex = false := by
  simp [ramseyEdge]

theorem ramseyEdge_comm (order : Nat) (coloring : Nat → Bool)
    (left right : Nat) :
    ramseyEdge order coloring left right =
      ramseyEdge order coloring right left := by
  by_cases hleftRight : left < right
  · have hnotRightLeft : ¬ right < left := by omega
    simp [ramseyEdge, hleftRight, hnotRightLeft]
  · by_cases hrightLeft : right < left
    · simp [ramseyEdge, hleftRight, hrightLeft]
    · have hequal : left = right := by omega
      subst right
      simp

/-- Pairwise relation on all distinct vertices of a list. -/
def AllDistinctRelated (relation : Nat → Nat → Bool)
    (vertices : List Nat) : Prop :=
  ∀ left, left ∈ vertices → ∀ right, right ∈ vertices → left ≠ right →
    relation left right = true

theorem allDistinctRelated_cons
    {relation : Nat → Nat → Bool} {head : Nat} {tail : List Nat}
    (hsymmetric : ∀ left right, relation left right = relation right left)
    (htail : AllDistinctRelated relation tail)
    (hhead : ∀ vertex, vertex ∈ tail → relation head vertex = true) :
    AllDistinctRelated relation (head :: tail) := by
  intro left hleft right hright hne
  simp only [List.mem_cons] at hleft hright
  rcases hleft with rfl | hleft
  · rcases hright with rfl | hright
    · exact absurd rfl hne
    · exact hhead right hright
  · rcases hright with rfl | hright
    · rw [hsymmetric left right]
      exact hhead left hleft
    · exact htail left hleft right hright hne

abbrev LocalVertex := Fin 25
abbrev AmbientVertex := Fin 43

/-- Upper-triangle pairs in the row-major order used by `edgeVar 25`. -/
def localEdgePairs : List (LocalVertex × LocalVertex) :=
  (List.finRange 25).flatMap fun left =>
    (List.finRange 25).filterMap fun right =>
      if left < right then some (left, right) else none

/-- Total decoder for local edge-variable indices. -/
def localEdgePair (index : Nat) : LocalVertex × LocalVertex :=
  localEdgePairs.getD index (0, 0)

/-- Executable round trip for the 300 genuine edge variables of `K₂₅`. -/
theorem localEdgePair_edgeVar (left right : LocalVertex)
    (hordered : left < right) :
    localEdgePair (edgeVar 25 left.val right.val) = (left, right) := by
  native_decide +revert

/-- If `flip` is true, complement the induced ambient coloring. -/
def inducedColoring (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool) (index : Nat) : Bool :=
  let endpoints := localEdgePair index
  let ambient := ramseyEdge 43 coloring
    (embedding endpoints.1).val (embedding endpoints.2).val
  if flip then !ambient else ambient

theorem inducedColoring_edgeVar
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool)
    (left right : LocalVertex) (hordered : left < right) :
    inducedColoring embedding coloring flip
        (edgeVar 25 left.val right.val) =
      if flip then
        !(ramseyEdge 43 coloring (embedding left).val (embedding right).val)
      else
        ramseyEdge 43 coloring (embedding left).val (embedding right).val := by
  simp [inducedColoring, localEdgePair_edgeVar left right hordered]

/-- Extend a finite embedding to naturals.  The out-of-range branch is used
only to make injectivity global; semantic clique vertices are all below 25. -/
def embedNat (embedding : LocalVertex → AmbientVertex) (vertex : Nat) : Nat :=
  if hvertex : vertex < 25 then
    (embedding ⟨vertex, hvertex⟩).val
  else
    43 + vertex

@[simp] theorem embedNat_of_lt (embedding : LocalVertex → AmbientVertex)
    {vertex : Nat} (hvertex : vertex < 25) :
    embedNat embedding vertex = (embedding ⟨vertex, hvertex⟩).val := by
  simp [embedNat, hvertex]

theorem embedNat_bound (embedding : LocalVertex → AmbientVertex)
    {vertex : Nat} (hvertex : vertex < 25) :
    embedNat embedding vertex < 43 := by
  rw [embedNat_of_lt embedding hvertex]
  exact (embedding ⟨vertex, hvertex⟩).isLt

theorem embedNat_injective (embedding : LocalVertex → AmbientVertex)
    (hinjective : Function.Injective embedding) :
    Function.Injective (embedNat embedding) := by
  intro left right hequal
  by_cases hleft : left < 25
  · by_cases hright : right < 25
    · have hfin : embedding ⟨left, hleft⟩ = embedding ⟨right, hright⟩ := by
        apply Fin.ext
        simpa [embedNat, hleft, hright] using hequal
      exact congrArg Fin.val (hinjective hfin)
    · have hleftBound := embedNat_bound embedding hleft
      have hrightValue : embedNat embedding right = 43 + right := by
        simp [embedNat, hright]
      omega
  · by_cases hright : right < 25
    · have hleftValue : embedNat embedding left = 43 + left := by
        simp [embedNat, hleft]
      have hrightBound := embedNat_bound embedding hright
      omega
    · simpa [embedNat, hleft, hright] using hequal

theorem mapped_nodup (embedding : LocalVertex → AmbientVertex)
    (hinjective : Function.Injective embedding)
    {vertices : List Nat} (hnodup : vertices.Nodup) :
    (vertices.map (embedNat embedding)).Nodup := by
  exact hnodup.map (embedNat embedding)
    (fun left right hne hequal =>
      hne (embedNat_injective embedding hinjective hequal))

theorem mapped_bound (embedding : LocalVertex → AmbientVertex)
    {vertices : List Nat}
    (hbound : ∀ vertex, vertex ∈ vertices → vertex < 25) :
    ∀ vertex, vertex ∈ vertices.map (embedNat embedding) → vertex < 43 := by
  intro vertex hvertex
  obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvertex
  exact embedNat_bound embedding (hbound index hindex)

theorem ramseyEdge_inducedColoring
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool)
    (left right : LocalVertex) (hne : left ≠ right) :
    ramseyEdge 25 (inducedColoring embedding coloring flip)
        left.val right.val =
      if flip then
        !(ramseyEdge 43 coloring (embedding left).val (embedding right).val)
      else
        ramseyEdge 43 coloring (embedding left).val (embedding right).val := by
  rcases Nat.lt_trichotomy left.val right.val with hordered | hequal | hreverse
  · simpa [ramseyEdge, hordered] using
      inducedColoring_edgeVar embedding coloring flip left right hordered
  · exact absurd (Fin.ext hequal) hne
  · have hreverseFin : right < left := hreverse
    rw [ramseyEdge_comm 25 (inducedColoring embedding coloring flip)]
    rw [ramseyEdge_comm 43 coloring]
    simpa [ramseyEdge, hreverse] using
      inducedColoring_edgeVar embedding coloring flip right left hreverseFin

theorem normalizedEdge_comm (coloring : Nat → Bool) (flip : Bool)
    (left right : Nat) :
    (if flip then !(ramseyEdge 43 coloring left right)
      else ramseyEdge 43 coloring left right) =
    (if flip then !(ramseyEdge 43 coloring right left)
      else ramseyEdge 43 coloring right left) := by
  rw [ramseyEdge_comm 43 coloring left right]

theorem local_true_related
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool)
    {vertices : List Nat}
    (_hbound : ∀ vertex, vertex ∈ vertices → vertex < 25)
    (hall : ∀ i j, i ∈ vertices → j ∈ vertices → i < j →
      inducedColoring embedding coloring flip (edgeVar 25 i j) = true) :
    AllDistinctRelated
      (ramseyEdge 25 (inducedColoring embedding coloring flip)) vertices := by
  intro left hleft right hright hne
  rcases Nat.lt_or_gt_of_ne hne with hordered | hreverse
  · simpa [ramseyEdge, hordered] using
      hall left right hleft hright hordered
  · rw [ramseyEdge_comm]
    simpa [ramseyEdge, hreverse] using
      hall right left hright hleft hreverse

theorem local_false_related
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool)
    {vertices : List Nat}
    (_hbound : ∀ vertex, vertex ∈ vertices → vertex < 25)
    (hall : ∀ i j, i ∈ vertices → j ∈ vertices → i < j →
      inducedColoring embedding coloring flip (edgeVar 25 i j) = false) :
    AllDistinctRelated
      (fun left right =>
        !(ramseyEdge 25 (inducedColoring embedding coloring flip) left right))
      vertices := by
  intro left hleft right hright hne
  rcases Nat.lt_or_gt_of_ne hne with hordered | hreverse
  · have hedge := hall left right hleft hright hordered
    simp [ramseyEdge, hordered, hedge]
  · change Bool.not
      (ramseyEdge 25 (inducedColoring embedding coloring flip) left right) = true
    rw [ramseyEdge_comm 25 (inducedColoring embedding coloring flip)]
    have hedge := hall right left hright hleft hreverse
    simp [ramseyEdge, hreverse, hedge]

theorem mapped_true_related
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool)
    {vertices : List Nat}
    (hbound : ∀ vertex, vertex ∈ vertices → vertex < 25)
    (hrelated : AllDistinctRelated
      (ramseyEdge 25 (inducedColoring embedding coloring flip)) vertices) :
    AllDistinctRelated
      (fun left right =>
        if flip then !(ramseyEdge 43 coloring left right)
        else ramseyEdge 43 coloring left right)
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
  have hedge := ramseyEdge_inducedColoring embedding coloring flip
    ⟨indexLeft, hleftBound⟩ ⟨indexRight, hrightBound⟩ (by
      intro hequal
      exact hindexNe (congrArg Fin.val hequal))
  rw [embedNat_of_lt embedding hleftBound,
    embedNat_of_lt embedding hrightBound]
  rw [hedge] at hlocal
  simpa using hlocal

theorem mapped_false_related
    (embedding : LocalVertex → AmbientVertex)
    (coloring : Nat → Bool) (flip : Bool)
    {vertices : List Nat}
    (hbound : ∀ vertex, vertex ∈ vertices → vertex < 25)
    (hrelated : AllDistinctRelated
      (fun left right =>
        !(ramseyEdge 25 (inducedColoring embedding coloring flip) left right))
      vertices) :
    AllDistinctRelated
      (fun left right =>
        !(if flip then !(ramseyEdge 43 coloring left right)
          else ramseyEdge 43 coloring left right))
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
  have hedge := ramseyEdge_inducedColoring embedding coloring flip
    ⟨indexLeft, hleftBound⟩ ⟨indexRight, hrightBound⟩ (by
      intro hequal
      exact hindexNe (congrArg Fin.val hequal))
  rw [embedNat_of_lt embedding hleftBound,
    embedNat_of_lt embedding hrightBound]
  change Bool.not (ramseyEdge 25 (inducedColoring embedding coloring flip)
    indexLeft indexRight) = true at hlocal
  rw [hedge] at hlocal
  simpa using hlocal

/-- Restrict a `K₅/K₅`-free coloring to 25 same-colour neighbours of a
root.  With `flip = false` these are red neighbours; with `flip = true`
they are blue neighbours and the restricted coloring is complemented. -/
theorem induced_isRamseyFree
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 43 5 5 coloring)
    (embedding : LocalVertex → AmbientVertex)
    (hinjective : Function.Injective embedding)
    (root : AmbientVertex) (flip : Bool)
    (hrootNe : ∀ index, root.val ≠ (embedding index).val)
    (hneighbour : ∀ index,
      ramseyEdge 43 coloring root.val (embedding index).val = !flip) :
    isRamseyFree 25 4 5 (inducedColoring embedding coloring flip) := by
  constructor
  · intro vertices hlength hbound hnodup hall
    let mapped := vertices.map (embedNat embedding)
    let forbidden := root.val :: mapped
    have hmappedNodup : mapped.Nodup := by
      exact mapped_nodup embedding hinjective hnodup
    have hmappedBound : ∀ vertex, vertex ∈ mapped → vertex < 43 := by
      exact mapped_bound embedding hbound
    have hrootNotMapped : root.val ∉ mapped := by
      intro hmem
      obtain ⟨index, hindex, hequal⟩ := List.mem_map.mp hmem
      have hindexBound := hbound index hindex
      have hequal' : root.val = (embedding ⟨index, hindexBound⟩).val := by
        simpa [embedNat, hindexBound] using hequal.symm
      exact hrootNe ⟨index, hindexBound⟩ hequal'
    have hforbiddenLength : forbidden.length = 5 := by
      simp [forbidden, mapped, hlength]
    have hforbiddenBound :
        ∀ vertex, vertex ∈ forbidden → vertex < 43 := by
      intro vertex hvertex
      simp only [forbidden, List.mem_cons] at hvertex
      rcases hvertex with rfl | hvertex
      · exact root.isLt
      · exact hmappedBound vertex hvertex
    have hforbiddenNodup : forbidden.Nodup := by
      simp only [forbidden, List.nodup_cons]
      exact ⟨hrootNotMapped, hmappedNodup⟩
    have hlocal := local_true_related embedding coloring flip hbound hall
    have hmapped := mapped_true_related embedding coloring flip hbound hlocal
    cases flip with
    | false =>
        have hmappedRed :
            AllDistinctRelated (ramseyEdge 43 coloring) mapped := by
          simpa using hmapped
        have hforbiddenRed :
            AllDistinctRelated (ramseyEdge 43 coloring) forbidden := by
          apply allDistinctRelated_cons
          · exact ramseyEdge_comm 43 coloring
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
            AllDistinctRelated
              (fun left right => !(ramseyEdge 43 coloring left right))
              mapped := by
          simpa using hmapped
        have hforbiddenBlue :
            AllDistinctRelated
              (fun left right => !(ramseyEdge 43 coloring left right))
              forbidden := by
          apply allDistinctRelated_cons
          · intro left right
            rw [ramseyEdge_comm 43 coloring left right]
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
    have hmappedNodup : mapped.Nodup := by
      exact mapped_nodup embedding hinjective hnodup
    have hmappedBound : ∀ vertex, vertex ∈ mapped → vertex < 43 := by
      exact mapped_bound embedding hbound
    have hlocal := local_false_related embedding coloring flip hbound hall
    have hmapped := mapped_false_related embedding coloring flip hbound hlocal
    cases flip with
    | false =>
        have hmappedBlue :
            AllDistinctRelated
              (fun left right => !(ramseyEdge 43 coloring left right))
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
            AllDistinctRelated (ramseyEdge 43 coloring) mapped := by
          simpa using hmapped
        apply hfree.1 mapped (by simp [mapped, hlength]) hmappedBound
          hmappedNodup
        intro left right hleft hright hordered
        have hedge := hmappedRed left hleft right hright
          (Nat.ne_of_lt hordered)
        simpa [ramseyEdge, hordered] using hedge

/-! ## Canonical neighbourhoods and the degree bound -/

/-- All in-range vertices other than `root` joined to it in the requested
colour.  `true` means red and `false` means blue. -/
def colorNeighbors (coloring : Nat → Bool) (root : Nat)
    (color : Bool) : List Nat :=
  (List.range 43).filter fun vertex =>
    decide (vertex ≠ root ∧ ramseyEdge 43 coloring root vertex = color)

@[simp] theorem mem_colorNeighbors (coloring : Nat → Bool)
    (root vertex : Nat) (color : Bool) :
    vertex ∈ colorNeighbors coloring root color ↔
      vertex < 43 ∧ vertex ≠ root ∧
        ramseyEdge 43 coloring root vertex = color := by
  simp [colorNeighbors]

theorem colorNeighbors_nodup (coloring : Nat → Bool) (root : Nat)
    (color : Bool) :
    (colorNeighbors coloring root color).Nodup := by
  exact (List.nodup_range (n := 43)).filter _

/-- The neighbour at local index `0, …, 24`, available whenever the
requested colour degree is at least 25. -/
def chosenNeighbor (coloring : Nat → Bool) (root : Nat) (color : Bool)
    (hlength : 25 ≤ (colorNeighbors coloring root color).length)
    (index : LocalVertex) : Nat :=
  (colorNeighbors coloring root color)[index.val]'(by
    exact Nat.lt_of_lt_of_le index.isLt hlength)

theorem chosenNeighbor_mem (coloring : Nat → Bool) (root : Nat)
    (color : Bool)
    (hlength : 25 ≤ (colorNeighbors coloring root color).length)
    (index : LocalVertex) :
    chosenNeighbor coloring root color hlength index ∈
      colorNeighbors coloring root color := by
  exact List.getElem_mem _

/-- The first 25 requested-colour neighbours, as an embedding into `K₄₃`. -/
def neighborEmbedding (coloring : Nat → Bool) (root : Nat) (color : Bool)
    (hlength : 25 ≤ (colorNeighbors coloring root color).length) :
    LocalVertex → AmbientVertex := fun index =>
  ⟨chosenNeighbor coloring root color hlength index,
    (mem_colorNeighbors coloring root
      (chosenNeighbor coloring root color hlength index) color).mp
        (chosenNeighbor_mem coloring root color hlength index) |>.1⟩

theorem neighborEmbedding_injective (coloring : Nat → Bool)
    (root : Nat) (color : Bool)
    (hlength : 25 ≤ (colorNeighbors coloring root color).length) :
    Function.Injective (neighborEmbedding coloring root color hlength) := by
  intro left right hequal
  apply Fin.ext
  have hvalues := congrArg Fin.val hequal
  exact (List.getElem_inj (colorNeighbors_nodup coloring root color)).mp hvalues

theorem neighborEmbedding_ne_root (coloring : Nat → Bool)
    (root : Nat) (color : Bool)
    (hlength : 25 ≤ (colorNeighbors coloring root color).length)
    (index : LocalVertex) :
    root ≠ (neighborEmbedding coloring root color hlength index).val := by
  have hmem := chosenNeighbor_mem coloring root color hlength index
  have hne := (mem_colorNeighbors coloring root
    (chosenNeighbor coloring root color hlength index) color).mp hmem |>.2.1
  exact hne.symm

theorem neighborEmbedding_color (coloring : Nat → Bool)
    (root : Nat) (color : Bool)
    (hlength : 25 ≤ (colorNeighbors coloring root color).length)
    (index : LocalVertex) :
    ramseyEdge 43 coloring root
      (neighborEmbedding coloring root color hlength index).val = color := by
  have hmem := chosenNeighbor_mem coloring root color hlength index
  exact (mem_colorNeighbors coloring root
    (chosenNeighbor coloring root color hlength index) color).mp hmem |>.2.2

/-- A `K₅/K₅`-free `K₄₃` coloring cannot give one vertex 25 neighbours
of a fixed colour.  Blue neighbourhoods are complemented before applying
the asymmetric input `R(4,5) ≤ 25`. -/
theorem colorNeighbors_length_le_twentyFour
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 43 5 5 coloring)
    (hR45 : ¬ hasRamseyFreeColoring 25 4 5)
    (root : Nat) (hroot : root < 43) (flip : Bool) :
    (colorNeighbors coloring root (!flip)).length ≤ 24 := by
  by_cases hlength :
      25 ≤ (colorNeighbors coloring root (!flip)).length
  · exfalso
    let embedding := neighborEmbedding coloring root (!flip) hlength
    have hinjective : Function.Injective embedding := by
      exact neighborEmbedding_injective coloring root (!flip) hlength
    have hrootNe : ∀ index, root ≠ (embedding index).val := by
      exact neighborEmbedding_ne_root coloring root (!flip) hlength
    have hneighbour : ∀ index,
        ramseyEdge 43 coloring root (embedding index).val = !flip := by
      exact neighborEmbedding_color coloring root (!flip) hlength
    apply hR45
    exact ⟨inducedColoring embedding coloring flip,
      induced_isRamseyFree hfree embedding hinjective ⟨root, hroot⟩ flip
        hrootNe hneighbour⟩
  · omega

def redNeighbors (coloring : Nat → Bool) (root : Nat) : List Nat :=
  colorNeighbors coloring root true

def blueNeighbors (coloring : Nat → Bool) (root : Nat) : List Nat :=
  colorNeighbors coloring root false

theorem redDegree_le_twentyFour
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 43 5 5 coloring)
    (hR45 : ¬ hasRamseyFreeColoring 25 4 5)
    (root : Nat) (hroot : root < 43) :
    (redNeighbors coloring root).length ≤ 24 := by
  simpa [redNeighbors] using
    colorNeighbors_length_le_twentyFour hfree hR45 root hroot false

theorem blueDegree_le_twentyFour
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 43 5 5 coloring)
    (hR45 : ¬ hasRamseyFreeColoring 25 4 5)
    (root : Nat) (hroot : root < 43) :
    (blueNeighbors coloring root).length ≤ 24 := by
  simpa [blueNeighbors] using
    colorNeighbors_length_le_twentyFour hfree hR45 root hroot true

/-- Final reusable statement: every in-range vertex has red and blue
degree at most 24. -/
theorem allDegrees_le_twentyFour
    {coloring : Nat → Bool}
    (hfree : isRamseyFree 43 5 5 coloring)
    (hR45 : ¬ hasRamseyFreeColoring 25 4 5) :
    ∀ root, root < 43 →
      (redNeighbors coloring root).length ≤ 24 ∧
      (blueNeighbors coloring root).length ≤ 24 := by
  intro root hroot
  exact ⟨redDegree_le_twentyFour hfree hR45 root hroot,
    blueDegree_le_twentyFour hfree hR45 root hroot⟩

#print axioms allDegrees_le_twentyFour

end LRATCatcher.Tests.R55DegreeBounds
