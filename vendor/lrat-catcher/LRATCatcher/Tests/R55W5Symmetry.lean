import LRATCatcher.Showcases.Ramsey

/-!
  Finite semantic audit of the W5 signature symmetry break used by the hard
  d=20,c=10,type=312 branch.  It checks all 320 automorphisms and all 1024
  ten-bit signatures, independently of the SAT encoding.
-/

namespace LRATCatcher.Tests.R55W5

open LRATCatcher.Ramsey

abbrev Permutation := List Nat
abbrev Signature := List Bool

def w5 : List Nat := [30, 609, 609, 897, 897, 390, 390, 120, 120, 30]

def twinPairs : List (Nat × Nat) :=
  [(0, 9), (1, 2), (5, 6), (7, 8), (3, 4)]

def pairIndex (vertex : Nat) : Nat :=
  if vertex == 0 || vertex == 9 then 0
  else if vertex == 1 || vertex == 2 then 1
  else if vertex == 5 || vertex == 6 then 2
  else if vertex == 7 || vertex == 8 then 3
  else 4

def pairSlot (vertex : Nat) : Nat :=
  let pair := twinPairs.getD (pairIndex vertex) (0, 0)
  if vertex == pair.1 then 0 else 1

def pairVertex (index slot : Nat) : Nat :=
  let pair := twinPairs.getD index (0, 0)
  if slot == 0 then pair.1 else pair.2

def dihedralPermutation (reflected : Bool) (shift : Nat) : Permutation :=
  (List.range 10).map fun vertex =>
    let sourcePair := pairIndex vertex
    let targetPair :=
      if reflected then (shift + 5 - sourcePair) % 5
      else (shift + sourcePair) % 5
    pairVertex targetPair (pairSlot vertex)

def dihedralPermutations : List Permutation :=
  [false, true].flatMap fun reflected =>
    (List.range 5).map fun shift => dihedralPermutation reflected shift

def twinSwapPermutation (mask : Nat) : Permutation :=
  (List.range 10).map fun vertex =>
    if mask.testBit (pairIndex vertex) then
      pairVertex (pairIndex vertex) (1 - pairSlot vertex)
    else vertex

def compose (left right : Permutation) : Permutation :=
  (List.range 10).map fun vertex =>
    left.getD (right.getD vertex 10) 10

def fullGroup : List Permutation :=
  dihedralPermutations.flatMap fun dihedral =>
    (List.range 32).map fun mask =>
      compose (twinSwapPermutation mask) dihedral

def isPermutation (permutation : Permutation) : Bool :=
  permutation.length == 10 &&
    (List.range 10).all fun target => permutation.count target == 1

def edge (graph : List Nat) (left right : Nat) : Bool :=
  (graph.getD left 0).testBit right

def preservesW5 (permutation : Permutation) : Bool :=
  isPermutation permutation &&
    (subsets 10 2).all fun vertices =>
      match vertices with
      | [left, right] =>
          edge w5 left right ==
            edge w5
              (permutation.getD left 10)
              (permutation.getD right 10)
      | _ => false

def signature (packed : Nat) : Signature :=
  (List.range 10).map packed.testBit

def transform (value : Signature) (permutation : Permutation) : Signature :=
  (List.range 10).map fun index =>
    value.getD (permutation.getD index 10) false

def lexLE : Signature → Signature → Bool
  | [], _ => true
  | _ :: _, [] => false
  | left :: lefts, right :: rights =>
      (!left && right) || (left == right && lexLE lefts rights)

def pairSorted (value : Signature) : Bool :=
  twinPairs.all fun pair =>
    !value.getD pair.1 false || value.getD pair.2 false

def dihedralMinimal (value : Signature) : Bool :=
  dihedralPermutations.drop 1 |>.all fun permutation =>
    lexLE value (transform value permutation)

def fullOrbitMinimal (value : Signature) : Bool :=
  fullGroup.all fun permutation =>
    lexLE value (transform value permutation)

def orbitHasAcceptedSignature (value : Signature) : Bool :=
  fullGroup.any fun permutation =>
    let transformed := transform value permutation
    pairSorted transformed && dihedralMinimal transformed

def acceptedSignatureCount : Nat :=
  (List.range 1024).countP fun packed =>
    pairSorted (signature packed) && dihedralMinimal (signature packed)

def checkW5Symmetry : Bool :=
  dihedralPermutations.length == 10 &&
    fullGroup.length == 320 &&
    fullGroup.eraseDups.length == 320 &&
    fullGroup.all preservesW5 &&
    acceptedSignatureCount == 39 &&
    (List.range 1024).all fun packed =>
      let value := signature packed
      (pairSorted value && dihedralMinimal value) == fullOrbitMinimal value &&
        orbitHasAcceptedSignature value

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem w5_signature_symmetry_checked : checkW5Symmetry = true := by
  native_decide

#print axioms w5_signature_symmetry_checked

end LRATCatcher.Tests.R55W5
