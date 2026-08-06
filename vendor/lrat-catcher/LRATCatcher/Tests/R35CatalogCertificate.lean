import LRATCatcher.Showcases.Ramsey
import LRATCatcher.Tests.R35CatalogData

/-!
  Machine-checked extension certificate for the complete R(3,5,n)
  catalogues through n=10.

  For every catalogue representative of order n and every one-vertex
  neighbourhood mask, `validPairs` independently decides whether the
  extension still has no triangle and no independent set of size five.
  Every valid extension has an explicit permutation to a representative in
  the next catalogue.  Thus no graph-isomorphism program is in the checker.
-/

namespace LRATCatcher.Tests.R35

open LRATCatcher.Ramsey

def edge (graph : Graph) (left right : Nat) : Bool :=
  (graph.getD left 0).testBit right

def pairwise (relation : Nat → Nat → Bool) : List Nat → Bool
  | [] => true
  | vertex :: vertices =>
      vertices.all (relation vertex) && pairwise relation vertices

def wellFormedGraph (order : Nat) (graph : Graph) : Bool :=
  graph.length == order &&
    (List.range order).all (fun vertex =>
      decide (graph.getD vertex 0 < 2 ^ order) &&
        !(edge graph vertex vertex)) &&
    (subsets order 2).all fun vertices =>
      match vertices with
      | [left, right] => edge graph left right == edge graph right left
      | _ => false

def validGraph (graph : Graph) : Bool :=
  let noTriangle :=
    (subsets graph.length 3).all fun vertices =>
      !(pairwise (edge graph) vertices)
  let noIndependentFive :=
    (subsets graph.length 5).all fun vertices =>
      !(pairwise (fun left right => !(edge graph left right)) vertices)
  noTriangle && noIndependentFive

def validExtension (parent : Graph) (mask : Nat) : Bool :=
  let noNewTriangle :=
    (subsets parent.length 2).all fun vertices =>
      !(vertices.all mask.testBit && pairwise (edge parent) vertices)
  let noNewIndependentFive :=
    (subsets parent.length 4).all fun vertices =>
      !(vertices.all (fun vertex => !(mask.testBit vertex)) &&
        pairwise (fun left right => !(edge parent left right)) vertices)
  noNewTriangle && noNewIndependentFive

def extensionEdge (parent : Graph) (mask left right : Nat) : Bool :=
  let newVertex := parent.length
  if left == newVertex then
    mask.testBit right
  else if right == newVertex then
    mask.testBit left
  else
    edge parent left right

def isPermutation (permutation : List Nat) (order : Nat) : Bool :=
  permutation.length == order &&
    (List.range order).all fun target => permutation.count target == 1

def isExtensionIsomorphism
    (parent : Graph) (mask : Nat) (target : Graph)
    (permutation : List Nat) : Bool :=
  let order := parent.length + 1
  target.length == order &&
    isPermutation permutation order &&
    (subsets order 2).all fun vertices =>
      match vertices with
      | [left, right] =>
          extensionEdge parent mask left right ==
            edge target
              (permutation.getD left order)
              (permutation.getD right order)
      | _ => false

def validPairs (parents : List Graph) : List (Nat × Nat) :=
  (List.range parents.length).flatMap fun parentIndex =>
    let parent := parents.getD parentIndex []
    ((List.range (2 ^ parent.length)).filter fun mask =>
      validExtension parent mask).map fun mask => (parentIndex, mask)

def checkWitness
    (parents targets : List Graph) (pair : Nat × Nat)
    (witness : ExtensionWitness) : Bool :=
  witness.parent == pair.1 &&
    witness.mask == pair.2 &&
    decide (witness.target < targets.length) &&
    isExtensionIsomorphism
      (parents.getD witness.parent [])
      witness.mask
      (targets.getD witness.target [])
      witness.permutation

def checkTransition
    (parents targets : List Graph) (witnesses : List ExtensionWitness) : Bool :=
  let pairs := validPairs parents
  pairs.length == witnesses.length &&
    (pairs.zip witnesses).all fun pair =>
      checkWitness parents targets pair.1 pair.2

def checkCatalogues : Bool :=
  let catalogueDataValid :=
    (List.range catalogues.length).all fun order =>
      (catalogues.getD order []).all fun graph =>
        wellFormedGraph order graph && validGraph graph
  let transitionsValid :=
    (List.range extensionWitnesses.length).all fun order =>
      checkTransition
        (catalogues.getD order [])
        (catalogues.getD (order + 1) [])
        (extensionWitnesses.getD order [])
  catalogues.length == extensionWitnesses.length + 1 &&
    catalogueDataValid && transitionsValid

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem r35_catalogue_extensions_checked : checkCatalogues = true := by
  native_decide

#print axioms r35_catalogue_extensions_checked

end LRATCatcher.Tests.R35
