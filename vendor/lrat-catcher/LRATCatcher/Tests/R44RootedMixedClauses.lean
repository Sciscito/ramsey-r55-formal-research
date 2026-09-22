import LRATCatcher.Tests.R44RootedGen4416Semantics
import LRATCatcher.Tests.R35UpperBound

/-!
  # Semantic bridge for the rooted mixed clauses

  Vertices `0,...,6` form the left block, vertices `7,...,14` the
  anti-neighbour block, and vertex `15` is the root.  The order-eight
  catalogue representative stores the complement of the raw graph on the
  anti-neighbour block.
-/

namespace LRATCatcher.Tests.R44RootedMixedClauses

open Std.Sat
open LRATCatcher.Ramsey
open LRATCatcher.Tests.R35
open LRATCatcher.Tests.R44RootedR34Catalogue
open LRATCatcher.Tests.R44RootedGen4416Semantics

abbrev Vertex := Fin 16

/-- Upper-triangle pairs in the row-major order used by `edgeVar 16`. -/
def edgePairs : List (Vertex × Vertex) :=
  (List.finRange 16).flatMap fun left =>
    (List.finRange 16).filterMap fun right =>
      if left < right then some (left, right) else none

/-- Total decoder for the 120 edge variables of `K_16`. -/
def edgePair (index : Nat) : Vertex × Vertex :=
  edgePairs.getD index (0, 0)

theorem edgePair_edgeVar (left right : Vertex) (hordered : left < right) :
    edgePair (edgeVar 16 left.val right.val) = (left, right) := by
  native_decide +revert

/-- Raw edge value for an ordered pair of canonical vertex labels. -/
def canonicalOrderedEdge
    (leftSelector antiSelector mask left right : Nat) : Bool :=
  if right < 7 then
    edge (r34Catalogue7.getD leftSelector []) left right
  else if left < 7 then
    if right < 15 then
      maskBit mask (8 * left + (right - 7))
    else
      true
  else if right < 15 then
    !(edge (r34Catalogue8.getD antiSelector []) (left - 7) (right - 7))
  else
    false

/-- Canonical rooted coloring on `K_16`, total on all natural variable
indices.  Values outside the 120 actual edge variables use the decoder's
irrelevant default pair. -/
def canonicalColoring
    (leftSelector antiSelector mask index : Nat) : Bool :=
  let endpoints := edgePair index
  canonicalOrderedEdge leftSelector antiSelector mask
    endpoints.1.val endpoints.2.val

theorem canonicalColoring_edgeVar
    (leftSelector antiSelector mask : Nat)
    (left right : Vertex) (hordered : left < right) :
    canonicalColoring leftSelector antiSelector mask
        (edgeVar 16 left.val right.val) =
      canonicalOrderedEdge leftSelector antiSelector mask left.val right.val := by
  simp [canonicalColoring, edgePair_edgeVar left right hordered]

@[simp] theorem canonicalColoring_left_edge
    (leftSelector antiSelector mask left right : Nat)
    (hleft : left < right) (hright : right < 7) :
    canonicalColoring leftSelector antiSelector mask
        (edgeVar 16 left right) =
      edge (r34Catalogue7.getD leftSelector []) left right := by
  have hleft16 : left < 16 := by omega
  have hright16 : right < 16 := by omega
  have hfin : (⟨left, hleft16⟩ : Vertex) < ⟨right, hright16⟩ := by
    change left < right
    exact hleft
  rw [canonicalColoring_edgeVar _ _ _ _ _ hfin]
  simp [canonicalOrderedEdge, hright]

@[simp] theorem canonicalColoring_cross_edge
    (leftSelector antiSelector mask left anti : Nat)
    (hleft : left < 7) (hanti : anti < 8) :
    canonicalColoring leftSelector antiSelector mask
        (edgeVar 16 left (7 + anti)) =
      maskBit mask (8 * left + anti) := by
  have hleft16 : left < 16 := by omega
  have hright16 : 7 + anti < 16 := by omega
  have hordered :
      (⟨left, hleft16⟩ : Vertex) < ⟨7 + anti, hright16⟩ := by
    change left < 7 + anti
    omega
  have hnotRightLeft : ¬ 7 + anti < 7 := by omega
  have hrightAnti : 7 + anti < 15 := by omega
  rw [canonicalColoring_edgeVar _ _ _ _ _ hordered]
  simp [canonicalOrderedEdge, hleft, hnotRightLeft, hrightAnti]

@[simp] theorem canonicalColoring_anti_edge
    (leftSelector antiSelector mask left right : Nat)
    (hleft : left < right) (hleftBound : left < 8)
    (hrightBound : right < 8) :
    canonicalColoring leftSelector antiSelector mask
        (edgeVar 16 (7 + left) (7 + right)) =
      !(edge (r34Catalogue8.getD antiSelector []) left right) := by
  have hleft16 : 7 + left < 16 := by omega
  have hright16 : 7 + right < 16 := by omega
  have hordered :
      (⟨7 + left, hleft16⟩ : Vertex) < ⟨7 + right, hright16⟩ := by
    change 7 + left < 7 + right
    omega
  have hnotRightLeft : ¬ 7 + right < 7 := by omega
  have hnotLeftLeft : ¬ 7 + left < 7 := by omega
  have hrightAnti : 7 + right < 15 := by omega
  rw [canonicalColoring_edgeVar _ _ _ _ _ hordered]
  simp [canonicalOrderedEdge, hnotRightLeft, hnotLeftLeft, hrightAnti]

@[simp] theorem canonicalColoring_left_root
    (leftSelector antiSelector mask left : Nat) (hleft : left < 7) :
    canonicalColoring leftSelector antiSelector mask
        (edgeVar 16 left 15) = true := by
  have hleft16 : left < 16 := by omega
  have hordered : (⟨left, hleft16⟩ : Vertex) < ⟨15, by omega⟩ := by
    change left < 15
    omega
  rw [canonicalColoring_edgeVar _ _ _ _ _ hordered]
  simp [canonicalOrderedEdge, hleft]

@[simp] theorem canonicalColoring_anti_root
    (leftSelector antiSelector mask anti : Nat) (hanti : anti < 8) :
    canonicalColoring leftSelector antiSelector mask
        (edgeVar 16 (7 + anti) 15) = false := by
  have hanti16 : 7 + anti < 16 := by omega
  have hordered : (⟨7 + anti, hanti16⟩ : Vertex) < ⟨15, by omega⟩ := by
    change 7 + anti < 15
    omega
  rw [canonicalColoring_edgeVar _ _ _ _ _ hordered]
  simp [canonicalOrderedEdge]

/-! ## Four-vertex semantic helpers -/

theorem false_of_red_four
    (coloring : Nat -> Bool) (hfree : isRamseyFree 16 4 4 coloring)
    (first second third fourth : Nat)
    (hfirst : first < second) (hsecond : second < third)
    (hthird : third < fourth) (hfourth : fourth < 16)
    (h01 : coloring (edgeVar 16 first second) = true)
    (h02 : coloring (edgeVar 16 first third) = true)
    (h03 : coloring (edgeVar 16 first fourth) = true)
    (h12 : coloring (edgeVar 16 second third) = true)
    (h13 : coloring (edgeVar 16 second fourth) = true)
    (h23 : coloring (edgeVar 16 third fourth) = true) : False := by
  have hnotRed := hfree.1 [first, second, third, fourth]
    (by simp) (by simp; omega) (by simp; omega)
  apply hnotRed
  intro i j hi hj hij
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hj
  rcases hi with rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl
  all_goals try omega
  all_goals assumption

theorem false_of_blue_four
    (coloring : Nat -> Bool) (hfree : isRamseyFree 16 4 4 coloring)
    (first second third fourth : Nat)
    (hfirst : first < second) (hsecond : second < third)
    (hthird : third < fourth) (hfourth : fourth < 16)
    (h01 : coloring (edgeVar 16 first second) = false)
    (h02 : coloring (edgeVar 16 first third) = false)
    (h03 : coloring (edgeVar 16 first fourth) = false)
    (h12 : coloring (edgeVar 16 second third) = false)
    (h13 : coloring (edgeVar 16 second fourth) = false)
    (h23 : coloring (edgeVar 16 third fourth) = false) : False := by
  have hnotBlue := hfree.2 [first, second, third, fourth]
    (by simp) (by simp; omega) (by simp; omega)
  apply hnotBlue
  intro i j hi hj hij
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hj
  rcases hi with rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl
  all_goals try omega
  all_goals assumption

/-! ## Extensionality in the cross mask -/

def canonicalGraph
    (leftSelector antiSelector mask : Nat) : Graph :=
  coloringGraph 16 (canonicalColoring leftSelector antiSelector mask)

theorem canonicalColoring_eq_of_maskBits_eq
    (leftSelector antiSelector firstMask secondMask : Nat)
    (hbits : forall bit, bit < 56 ->
      maskBit firstMask bit = maskBit secondMask bit) :
    canonicalColoring leftSelector antiSelector firstMask =
      canonicalColoring leftSelector antiSelector secondMask := by
  funext index
  dsimp [canonicalColoring]
  unfold canonicalOrderedEdge
  split <;> try rfl
  split <;> try rfl
  split <;> try rfl
  apply hbits
  omega
  all_goals skip
  all_goals skip
  /-
    ? split <;> rfl
  -/

theorem canonicalGraph_eq_of_maskBits_eq
    (leftSelector antiSelector firstMask secondMask : Nat)
    (hbits : forall bit, bit < 56 ->
      maskBit firstMask bit = maskBit secondMask bit) :
    canonicalGraph leftSelector antiSelector firstMask =
      canonicalGraph leftSelector antiSelector secondMask := by
  unfold canonicalGraph
  rw [canonicalColoring_eq_of_maskBits_eq
    leftSelector antiSelector firstMask secondMask hbits]

/-! ## The four mixed Ramsey obstructions -/

def K4OneLeftThreeAntiValid
    (leftSelector antiSelector mask : Nat) : Prop :=
  forall left first second third,
    left < 7 -> first < second -> second < third -> third < 8 ->
    isIndependent (r34Catalogue8.getD antiSelector [])
      [first, second, third] = true ->
    Not (And (maskBit mask (8 * left + first) = true)
      (And (maskBit mask (8 * left + second) = true)
        (maskBit mask (8 * left + third) = true)))


theorem ramseyFree_k4OneLeftThreeAnti
    (leftSelector antiSelector mask : Nat)
    (hfree :
      isRamseyFree 16 4 4
        (canonicalColoring leftSelector antiSelector mask)) :
    K4OneLeftThreeAntiValid leftSelector antiSelector mask := by
  intro left first second third hleft hfirst hsecond hthird hindependent
  intro hallCross
  simp [isIndependent, pythonCombinations] at hindependent
  have hfirstBound : first < 8 := by omega
  have hsecondBound : second < 8 := by omega
  have hnotRed := hfree.1
    [left, 7 + first, 7 + second, 7 + third]
    (by simp) (by simp; omega) (by simp; omega)
  apply hnotRed
  intro i j hi hj hij
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hj
  rcases hi with rfl | rfl | rfl | rfl <;>
    rcases hj with rfl | rfl | rfl | rfl
  all_goals try omega
  all_goals
    simp_all [canonicalColoring_cross_edge, canonicalColoring_anti_edge]

def K4TwoLeftTwoAntiValid
    (leftSelector antiSelector mask : Nat) : Prop :=
  forall leftFirst leftSecond antiFirst antiSecond,
    leftFirst < leftSecond -> leftSecond < 7 ->
    antiFirst < antiSecond -> antiSecond < 8 ->
    isClique (r34Catalogue7.getD leftSelector [])
      [leftFirst, leftSecond] = true ->
    isIndependent (r34Catalogue8.getD antiSelector [])
      [antiFirst, antiSecond] = true ->
    Not (And (maskBit mask (8 * leftFirst + antiFirst) = true)
      (And (maskBit mask (8 * leftFirst + antiSecond) = true)
        (And (maskBit mask (8 * leftSecond + antiFirst) = true)
          (maskBit mask (8 * leftSecond + antiSecond) = true))))

theorem ramseyFree_k4TwoLeftTwoAnti
    (leftSelector antiSelector mask : Nat)
    (hfree : isRamseyFree 16 4 4
      (canonicalColoring leftSelector antiSelector mask)) :
    K4TwoLeftTwoAntiValid leftSelector antiSelector mask := by
  intro leftFirst leftSecond antiFirst antiSecond
    hleftOrder hleftSecondBound hantiOrder hantiSecondBound
    hleftClique hantiIndependent
  intro hallCross
  have hleftFirstBound : leftFirst < 7 := by omega
  have hantiFirstBound : antiFirst < 8 := by omega
  simp [isClique, pythonCombinations] at hleftClique
  simp [isIndependent, pythonCombinations] at hantiIndependent
  have h01 : canonicalColoring leftSelector antiSelector mask
      (edgeVar 16 leftFirst leftSecond) = true := by
    rw [canonicalColoring_left_edge _ _ _ _ _
      hleftOrder hleftSecondBound]
    exact hleftClique
  have h02 : canonicalColoring leftSelector antiSelector mask
      (edgeVar 16 leftFirst (7 + antiFirst)) = true := by
    rw [canonicalColoring_cross_edge _ _ _ _ _
      hleftFirstBound hantiFirstBound]
    exact hallCross.1
  have h03 : canonicalColoring leftSelector antiSelector mask
      (edgeVar 16 leftFirst (7 + antiSecond)) = true := by
    rw [canonicalColoring_cross_edge _ _ _ _ _
      hleftFirstBound hantiSecondBound]
    exact hallCross.2.1
  have h12 : canonicalColoring leftSelector antiSelector mask
      (edgeVar 16 leftSecond (7 + antiFirst)) = true := by
    rw [canonicalColoring_cross_edge _ _ _ _ _
      hleftSecondBound hantiFirstBound]
    exact hallCross.2.2.1
  have h13 : canonicalColoring leftSelector antiSelector mask
      (edgeVar 16 leftSecond (7 + antiSecond)) = true := by
    rw [canonicalColoring_cross_edge _ _ _ _ _
      hleftSecondBound hantiSecondBound]
    exact hallCross.2.2.2
  have h23 : canonicalColoring leftSelector antiSelector mask
      (edgeVar 16 (7 + antiFirst) (7 + antiSecond)) = true := by
    rw [canonicalColoring_anti_edge _ _ _ _ _
      hantiOrder hantiFirstBound hantiSecondBound]
    simp [hantiIndependent]
  exact false_of_red_four
    (canonicalColoring leftSelector antiSelector mask) hfree
    leftFirst leftSecond (7 + antiFirst) (7 + antiSecond)
    hleftOrder (by omega) (by omega) (by omega)
    h01 h02 h03 h12 h13 h23

def I4ThreeLeftOneAntiValid
    (leftSelector antiSelector mask : Nat) : Prop :=
  forall leftFirst leftSecond leftThird anti,
    leftFirst < leftSecond -> leftSecond < leftThird ->
    leftThird < 7 -> anti < 8 ->
    isIndependent (r34Catalogue7.getD leftSelector [])
      [leftFirst, leftSecond, leftThird] = true ->
    Not (And (maskBit mask (8 * leftFirst + anti) = false)
      (And (maskBit mask (8 * leftSecond + anti) = false)
        (maskBit mask (8 * leftThird + anti) = false)))

theorem ramseyFree_i4ThreeLeftOneAnti
    (leftSelector antiSelector mask : Nat)
    (hfree : isRamseyFree 16 4 4
      (canonicalColoring leftSelector antiSelector mask)) :
    I4ThreeLeftOneAntiValid leftSelector antiSelector mask := by
  intro leftFirst leftSecond leftThird anti
    hfirstOrder hsecondOrder hthirdBound hantiBound hleftIndependent
  intro hallCross
  have hfirstBound : leftFirst < 7 := by omega
  have hsecondBound : leftSecond < 7 := by omega
  simp [isIndependent, pythonCombinations] at hleftIndependent
  have h01 : canonicalColoring leftSelector antiSelector mask
      (edgeVar 16 leftFirst leftSecond) = false := by
    rw [canonicalColoring_left_edge _ _ _ _ _
      hfirstOrder hsecondBound]
    exact hleftIndependent.1
  have h02 : canonicalColoring leftSelector antiSelector mask
      (edgeVar 16 leftFirst leftThird) = false := by
    rw [canonicalColoring_left_edge _ _ _ _ _
      (by omega) hthirdBound]
    exact hleftIndependent.2.1
  have h03 : canonicalColoring leftSelector antiSelector mask
      (edgeVar 16 leftFirst (7 + anti)) = false := by
    rw [canonicalColoring_cross_edge _ _ _ _ _ hfirstBound hantiBound]
    exact hallCross.1
  have h12 : canonicalColoring leftSelector antiSelector mask
      (edgeVar 16 leftSecond leftThird) = false := by
    rw [canonicalColoring_left_edge _ _ _ _ _
      hsecondOrder hthirdBound]
    exact hleftIndependent.2.2
  have h13 : canonicalColoring leftSelector antiSelector mask
      (edgeVar 16 leftSecond (7 + anti)) = false := by
    rw [canonicalColoring_cross_edge _ _ _ _ _ hsecondBound hantiBound]
    exact hallCross.2.1
  have h23 : canonicalColoring leftSelector antiSelector mask
      (edgeVar 16 leftThird (7 + anti)) = false := by
    rw [canonicalColoring_cross_edge _ _ _ _ _ hthirdBound hantiBound]
    exact hallCross.2.2
  exact false_of_blue_four
    (canonicalColoring leftSelector antiSelector mask) hfree
    leftFirst leftSecond leftThird (7 + anti)
    hfirstOrder hsecondOrder (by omega) (by omega)
    h01 h02 h03 h12 h13 h23

def I4TwoLeftTwoAntiValid
    (leftSelector antiSelector mask : Nat) : Prop :=
  forall leftFirst leftSecond antiFirst antiSecond,
    leftFirst < leftSecond -> leftSecond < 7 ->
    antiFirst < antiSecond -> antiSecond < 8 ->
    isIndependent (r34Catalogue7.getD leftSelector [])
      [leftFirst, leftSecond] = true ->
    isClique (r34Catalogue8.getD antiSelector [])
      [antiFirst, antiSecond] = true ->
    Not (And (maskBit mask (8 * leftFirst + antiFirst) = false)
      (And (maskBit mask (8 * leftFirst + antiSecond) = false)
        (And (maskBit mask (8 * leftSecond + antiFirst) = false)
          (maskBit mask (8 * leftSecond + antiSecond) = false))))

theorem ramseyFree_i4TwoLeftTwoAnti
    (leftSelector antiSelector mask : Nat)
    (hfree : isRamseyFree 16 4 4
      (canonicalColoring leftSelector antiSelector mask)) :
    I4TwoLeftTwoAntiValid leftSelector antiSelector mask := by
  intro leftFirst leftSecond antiFirst antiSecond
    hleftOrder hleftSecondBound hantiOrder hantiSecondBound
    hleftIndependent hantiClique
  intro hallCross
  have hleftFirstBound : leftFirst < 7 := by omega
  have hantiFirstBound : antiFirst < 8 := by omega
  simp [isIndependent, pythonCombinations] at hleftIndependent
  simp [isClique, pythonCombinations] at hantiClique
  have h01 : canonicalColoring leftSelector antiSelector mask
      (edgeVar 16 leftFirst leftSecond) = false := by
    rw [canonicalColoring_left_edge _ _ _ _ _
      hleftOrder hleftSecondBound]
    exact hleftIndependent
  have h02 : canonicalColoring leftSelector antiSelector mask
      (edgeVar 16 leftFirst (7 + antiFirst)) = false := by
    rw [canonicalColoring_cross_edge _ _ _ _ _
      hleftFirstBound hantiFirstBound]
    exact hallCross.1
  have h03 : canonicalColoring leftSelector antiSelector mask
      (edgeVar 16 leftFirst (7 + antiSecond)) = false := by
    rw [canonicalColoring_cross_edge _ _ _ _ _
      hleftFirstBound hantiSecondBound]
    exact hallCross.2.1
  have h12 : canonicalColoring leftSelector antiSelector mask
      (edgeVar 16 leftSecond (7 + antiFirst)) = false := by
    rw [canonicalColoring_cross_edge _ _ _ _ _
      hleftSecondBound hantiFirstBound]
    exact hallCross.2.2.1
  have h13 : canonicalColoring leftSelector antiSelector mask
      (edgeVar 16 leftSecond (7 + antiSecond)) = false := by
    rw [canonicalColoring_cross_edge _ _ _ _ _
      hleftSecondBound hantiSecondBound]
    exact hallCross.2.2.2
  have h23 : canonicalColoring leftSelector antiSelector mask
      (edgeVar 16 (7 + antiFirst) (7 + antiSecond)) = false := by
    rw [canonicalColoring_anti_edge _ _ _ _ _
      hantiOrder hantiFirstBound hantiSecondBound]
    simp [hantiClique]
  exact false_of_blue_four
    (canonicalColoring leftSelector antiSelector mask) hfree
    leftFirst leftSecond (7 + antiFirst) (7 + antiSecond)
    hleftOrder (by omega) (by omega) (by omega)
    h01 h02 h03 h12 h13 h23

/-- Semantic content of the four guarded mixed-clique families for the
selected catalogue pair. -/
structure MixedFamiliesValid
    (leftSelector antiSelector mask : Nat) : Prop where
  k4OneLeftThreeAnti :
    K4OneLeftThreeAntiValid leftSelector antiSelector mask
  k4TwoLeftTwoAnti :
    K4TwoLeftTwoAntiValid leftSelector antiSelector mask
  i4ThreeLeftOneAnti :
    I4ThreeLeftOneAntiValid leftSelector antiSelector mask
  i4TwoLeftTwoAnti :
    I4TwoLeftTwoAntiValid leftSelector antiSelector mask

theorem ramseyFree_mixedFamiliesValid
    (leftSelector antiSelector mask : Nat)
    (hfree : isRamseyFree 16 4 4
      (canonicalColoring leftSelector antiSelector mask)) :
    MixedFamiliesValid leftSelector antiSelector mask where
  k4OneLeftThreeAnti :=
    ramseyFree_k4OneLeftThreeAnti leftSelector antiSelector mask hfree
  k4TwoLeftTwoAnti :=
    ramseyFree_k4TwoLeftTwoAnti leftSelector antiSelector mask hfree
  i4ThreeLeftOneAnti :=
    ramseyFree_i4ThreeLeftOneAnti leftSelector antiSelector mask hfree
  i4TwoLeftTwoAnti :=
    ramseyFree_i4TwoLeftTwoAnti leftSelector antiSelector mask hfree

#print axioms canonicalColoring_eq_of_maskBits_eq
#print axioms ramseyFree_mixedFamiliesValid

end LRATCatcher.Tests.R44RootedMixedClauses
