import LRATCatcher.Tests.R35CatalogCompleteness
import LRATCatcher.Tests.R45DegreeEightCoverData

/-!
  # Certified left-hand cover for the R(4,5,25) degree-eight split

  The Barakeel `gen358` file has 27 partially coloured parents and 179 fully
  coloured children.  The generated data records the original base-3 graph
  identifiers, the stored parent/child permutations, a unique match to every
  representative of the independently certified `R(3,5,8)` catalogue, and
  the composed parent-to-catalogue permutation.

  The checker below reconstructs all base-3 edge colours and verifies every
  permutation and fixed parent edge.  The final semantic theorem composes
  this finite check with `r35_catalogues_complete`, so every valid order-eight
  graph is isomorphic to a catalogue representative entering one of the 27
  parents.  Linking the embedded decimal records byte-for-byte to the
  external `gen358` text remains an auditable generation/reproducibility step.
-/

namespace LRATCatcher.Tests.R45DegreeEightCover

open LRATCatcher.Tests.R35

abbrev order : Nat := 8
abbrev edgeCount : Nat := order * (order - 1) / 2

def r35Catalogue8 : List Graph := catalogues.getD order []

/-- Row-major upper-triangle index used by the HOL4 base-3 records. -/
def edgeIndex (left right : Nat) : Nat :=
  let low := min left right
  let high := max left right
  low * (2 * order - low - 1) / 2 + (high - low - 1)

/-- Decode one edge colour while leaving the leading base-3 sentinel intact. -/
def ternaryColourAt (encoded left right : Nat) : Nat :=
  (encoded / 3 ^ (edgeCount - 1 - edgeIndex left right)) % 3

def hasOrderEightSentinel (encoded : Nat) : Bool :=
  encoded / 3 ^ edgeCount == 1

def fullChild (encoded : Nat) : Bool :=
  (LRATCatcher.Ramsey.subsets order 2).all fun vertices =>
    match vertices with
    | [left, right] =>
        ternaryColourAt encoded left right == 1 ||
          ternaryColourAt encoded left right == 2
    | _ => false

def inverseAt (permutation : List Nat) (vertex : Nat) : Nat :=
  permutation.idxOf vertex

/-- Check the exact permutation convention stored by `normalize_nauty_wperm`. -/
def parentChildAgreement
    (parent child : Nat) (permutation : List Nat) : Bool :=
  isPermutation permutation order &&
    (LRATCatcher.Ramsey.subsets order 2).all fun vertices =>
      match vertices with
      | [left, right] =>
          let colour := ternaryColourAt parent left right
          colour == 0 ||
            colour == ternaryColourAt child
              (inverseAt permutation left) (inverseAt permutation right)
      | _ => false

def childCatalogueIsomorphism
    (child : Nat) (target : Graph) (permutation : List Nat) : Bool :=
  target.length == order && isPermutation permutation order &&
    (LRATCatcher.Ramsey.subsets order 2).all fun vertices =>
      match vertices with
      | [left, right] =>
          (ternaryColourAt child left right == 1) ==
            edge target
              (permutation.getD left order)
              (permutation.getD right order)
      | _ => false

/-- A partially coloured parent agrees with a materialized Lean graph after
the supplied relabeling.  HOL4 colour 1 is the Lean red/true edge. -/
def parentCatalogueAgreement
    (parent : Nat) (target : Graph) (permutation : List Nat) : Bool :=
  target.length == order && isPermutation permutation order &&
    (LRATCatcher.Ramsey.subsets order 2).all fun vertices =>
      match vertices with
      | [left, right] =>
          let colour := ternaryColourAt parent left right
          colour == 0 ||
            ((colour == 1) ==
              edge target
                (permutation.getD left order)
                (permutation.getD right order))
      | _ => false

def composedPermutation (witness : Gen358Witness) : List Nat :=
  (List.range order).map fun originalVertex =>
    witness.cataloguePermutation.getD
      (inverseAt witness.parentPermutation originalVertex) order

def checkSemanticWitness (target : Graph) (witness : Gen358Witness) : Bool :=
  decide (witness.parent < gen358ParentIds.length) &&
    parentCatalogueAgreement
      (gen358ParentIds.getD witness.parent 0)
      target witness.directPermutation

def checkWitness (targetIndex : Nat) (witness : Gen358Witness) : Bool :=
  let target := r35Catalogue8.getD targetIndex []
  checkSemanticWitness target witness &&
    (hasOrderEightSentinel (gen358ParentIds.getD witness.parent 0) &&
      hasOrderEightSentinel witness.childId &&
      fullChild witness.childId &&
      parentChildAgreement
        (gen358ParentIds.getD witness.parent 0)
        witness.childId witness.parentPermutation &&
      childCatalogueIsomorphism
        witness.childId target witness.cataloguePermutation &&
      witness.directPermutation == composedPermutation witness)

def checkGen358Witnesses : Bool :=
  r35Catalogue8.length == gen358Witnesses.length &&
    (List.range r35Catalogue8.length).all fun targetIndex =>
      checkWitness targetIndex (gen358Witnesses.getD targetIndex {
        parent := 0
        childId := 0
        parentPermutation := []
        cataloguePermutation := []
        directPermutation := []
      })

theorem gen358_parent_count : gen358ParentIds.length = 27 := by
  native_decide

theorem gen358_witness_count : gen358Witnesses.length = 179 := by
  native_decide

theorem gen358_parent_ids_unique : gen358ParentIds.Nodup := by
  native_decide

theorem gen358_child_ids_unique :
    (gen358Witnesses.map fun witness => witness.childId).Nodup := by
  native_decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gen358_witnesses_checked : checkGen358Witnesses = true := by
  native_decide

/-- The fixed colours of a `gen358` parent agree with a completed graph after
an explicit relabeling.  Keeping this permutation visible is essential for
the later block-diagonal relabeling of the degree-eight Ramsey branch. -/
def ParentMatches (parentId : Nat) (completion : Graph) : Prop :=
  ∃ permutation,
    parentCatalogueAgreement parentId completion permutation = true

/-- A graph is covered by a specific `gen358` parent when it is isomorphic to
a completion whose fixed edge colours match that parent. -/
def CoveredByGen358Parent
    (graph : Graph) (parentId : Nat) : Prop :=
  ∃ completion,
    GraphIsomorphicFin graph completion ∧ ParentMatches parentId completion

/-- A graph itself matches one of the 27 parents after relabeling. -/
def Gen358Covered (graph : Graph) : Prop :=
  ∃ parentIndex, parentIndex < gen358ParentIds.length ∧
    ParentMatches (gen358ParentIds.getD parentIndex 0) graph

theorem targetIndex_covered (targetIndex : Nat)
    (htarget : targetIndex < r35Catalogue8.length) :
    Gen358Covered (r35Catalogue8.getD targetIndex []) := by
  have hmember : targetIndex ∈ List.range r35Catalogue8.length :=
    List.mem_range.mpr htarget
  have hall := gen358_witnesses_checked
  unfold checkGen358Witnesses at hall
  rw [Bool.and_eq_true] at hall
  have hwitness := List.all_eq_true.mp hall.2 targetIndex hmember
  unfold checkWitness at hwitness
  rw [Bool.and_eq_true] at hwitness
  have hsemantic := hwitness.1
  unfold checkSemanticWitness at hsemantic
  rw [Bool.and_eq_true] at hsemantic
  exact ⟨(gen358Witnesses.getD targetIndex {
      parent := 0
      childId := 0
      parentPermutation := []
      cataloguePermutation := []
      directPermutation := []
    }).parent,
    of_decide_eq_true hsemantic.1,
    (gen358Witnesses.getD targetIndex {
      parent := 0
      childId := 0
      parentPermutation := []
      cataloguePermutation := []
      directPermutation := []
    }).directPermutation,
    hsemantic.2⟩

theorem catalogueMember_covered (representative : Graph)
    (hrepresentative : representative ∈ r35Catalogue8) :
    Gen358Covered representative := by
  obtain ⟨targetIndex, htarget, hget⟩ :=
    List.getElem_of_mem hrepresentative
  have hgetD : r35Catalogue8.getD targetIndex [] = representative := by
    rw [← List.getElem_eq_getD (l := r35Catalogue8) (i := targetIndex)
      (h := htarget) []]
    exact hget
  have hcovered := targetIndex_covered targetIndex htarget
  rw [hgetD] at hcovered
  exact hcovered

/-- Semantic left-cover theorem for the degree-eight split.  Unlike the raw
finite check, this starts with an arbitrary valid order-eight graph and
returns a concrete parent plus an isomorphic matching completion. -/
theorem every_r35_order_eight_graph_enters_gen358
    (graph : Graph) (hgraph : GraphValidAt order graph) :
    ∃ parentIndex, parentIndex < gen358ParentIds.length ∧
      CoveredByGen358Parent graph
        (gen358ParentIds.getD parentIndex 0) := by
  have hcomplete :
      StrongCatalogueComplete order r35Catalogue8 := by
    apply r35_catalogues_complete order
    rw [extensionWitnesses_length_eq_fourteen]
    change 8 ≤ 14
    omega
  obtain ⟨representative, hrepresentative, hisomorphic⟩ :=
    hcomplete graph hgraph
  obtain ⟨parentIndex, hparentIndex, hmatch⟩ :=
    catalogueMember_covered representative hrepresentative
  exact ⟨parentIndex, hparentIndex, representative, hisomorphic, hmatch⟩

#print axioms every_r35_order_eight_graph_enters_gen358

end LRATCatcher.Tests.R45DegreeEightCover
