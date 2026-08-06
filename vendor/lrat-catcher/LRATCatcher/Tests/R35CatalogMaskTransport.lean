import LRATCatcher.Tests.R35CatalogGraphIso
import LRATCatcher.Tests.R35CatalogExtensionProperties

/-!
  Transport of a one-vertex neighbourhood mask along `GraphIsoFin`.

  If `p : parent ≅ representative`, the bit at a target vertex `v` is the
  old bit at `p⁻¹(v)`.  Encoding these target-indexed bits through a `BitVec`
  gives the range bound for free and makes the bit law explicit.
-/

namespace LRATCatcher.Tests.R35

open LRATCatcher.Ramsey

/-- Target-indexed bit list obtained by pulling a mask back through `p⁻¹`. -/
def transportedMaskBits {parent representative : Graph}
    (isomorphism : GraphIsoFin parent representative) (mask : Nat) :
    List Bool :=
  (List.finRange isomorphism.order).map fun target =>
    mask.testBit (isomorphism.permutation.invFun target).val

/-- The transported mask, packed as a natural number. -/
def transportedMask {parent representative : Graph}
    (isomorphism : GraphIsoFin parent representative) (mask : Nat) : Nat :=
  (BitVec.ofBoolListLE (transportedMaskBits isomorphism mask)).toNat

@[simp] theorem transportedMaskBits_length
    {parent representative : Graph}
    (isomorphism : GraphIsoFin parent representative) (mask : Nat) :
    (transportedMaskBits isomorphism mask).length = isomorphism.order := by
  simp [transportedMaskBits]

/-- A transported mask is always in the exact finite range of the target. -/
theorem transportedMask_lt
    {parent representative : Graph}
    (isomorphism : GraphIsoFin parent representative) (mask : Nat) :
    transportedMask isomorphism mask < 2 ^ isomorphism.order := by
  unfold transportedMask
  simpa using
    (BitVec.ofBoolListLE (transportedMaskBits isomorphism mask)).isLt

/-- The same range bound stated with the representative's concrete length. -/
theorem transportedMask_lt_targetLength
    {parent representative : Graph}
    (isomorphism : GraphIsoFin parent representative) (mask : Nat) :
    transportedMask isomorphism mask < 2 ^ representative.length := by
  rw [isomorphism.targetOrder]
  exact transportedMask_lt isomorphism mask

/-- Reading a target bit gives the source bit at the inverse image. -/
theorem transportedMask_testBit_target
    {parent representative : Graph}
    (isomorphism : GraphIsoFin parent representative) (mask : Nat)
    (target : Fin isomorphism.order) :
    (transportedMask isomorphism mask).testBit target.val =
      mask.testBit (isomorphism.permutation.invFun target).val := by
  let bits := transportedMaskBits isomorphism mask
  have hindex : target.val < bits.length := by
    simp [bits]
  unfold transportedMask
  rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE]
  rw [← List.getElem_eq_getD (l := bits) (i := target.val)
    (h := hindex) false]
  simp [bits, transportedMaskBits]

/-- Natural-index form of the inverse-image bit law. -/
theorem transportedMask_testBit_targetNat
    {parent representative : Graph}
    (isomorphism : GraphIsoFin parent representative) (mask target : Nat)
    (htarget : target < representative.length) :
    (transportedMask isomorphism mask).testBit target =
      mask.testBit
        (isomorphism.permutation.invFun
          (Fin.cast isomorphism.targetOrder ⟨target, htarget⟩)).val := by
  let targetFin : Fin isomorphism.order :=
    Fin.cast isomorphism.targetOrder ⟨target, htarget⟩
  have := transportedMask_testBit_target isomorphism mask targetFin
  simpa [targetFin] using this

/-- Equivalently, the bit at the image of a source vertex is its old bit. -/
theorem transportedMask_testBit_image
    {parent representative : Graph}
    (isomorphism : GraphIsoFin parent representative) (mask : Nat)
    (source : Fin isomorphism.order) :
    (transportedMask isomorphism mask).testBit
        (isomorphism.permutation source).val =
      mask.testBit source.val := by
  rw [transportedMask_testBit_target]
  rw [isomorphism.permutation.left_inv]

namespace FinPermutation

/-- Extend a permutation by fixing one newly appended final vertex. -/
def extendFixed {order : Nat}
    (permutation : FinPermutation order) : FinPermutation (order + 1) where
  toFun := fun vertex =>
    Fin.lastCases (Fin.last order)
      (fun old => Fin.castSucc (permutation old)) vertex
  invFun := fun vertex =>
    Fin.lastCases (Fin.last order)
      (fun old => Fin.castSucc (permutation.invFun old)) vertex
  left_inv := by
    intro vertex
    refine Fin.lastCases ?_ (fun old => ?_) vertex
    · simp
    · simp [permutation.left_inv]
  right_inv := by
    intro vertex
    refine Fin.lastCases ?_ (fun old => ?_) vertex
    · simp
    · simp [permutation.right_inv]

@[simp] theorem extendFixed_last {order : Nat}
    (permutation : FinPermutation order) :
    permutation.extendFixed (Fin.last order) = Fin.last order := by
  simp [extendFixed]

@[simp] theorem extendFixed_castSucc {order : Nat}
    (permutation : FinPermutation order) (vertex : Fin order) :
    permutation.extendFixed (Fin.castSucc vertex) =
      Fin.castSucc (permutation vertex) := by
  simp [extendFixed]

end FinPermutation

/-! ## Adjacency in a materialized extension -/

theorem maskTransport_edge_extension_old_old
    (parent : Graph) (mask : Nat) (left right : Fin parent.length) :
    edge (extensionGraph parent mask) left.val right.val =
      edge parent left.val right.val := by
  simp only [edge]
  rw [extensionGraph_getD_old parent mask left.val left.isLt]
  have hrightNe : parent.length ≠ right.val := by omega
  cases hmask : mask.testBit left.val <;>
    simp [Nat.testBit_or, Nat.testBit_mod_two_pow, right.isLt, hrightNe]

theorem maskTransport_edge_extension_new_old
    (parent : Graph) (mask : Nat) (vertex : Fin parent.length) :
    edge (extensionGraph parent mask) parent.length vertex.val =
      mask.testBit vertex.val := by
  simp only [edge]
  rw [extensionGraph_getD_new]
  simp [Nat.testBit_mod_two_pow, vertex.isLt]

theorem maskTransport_edge_extension_old_new
    (parent : Graph) (mask : Nat) (vertex : Fin parent.length) :
    edge (extensionGraph parent mask) vertex.val parent.length =
      mask.testBit vertex.val := by
  simp only [edge]
  rw [extensionGraph_getD_old parent mask vertex.val vertex.isLt]
  cases hmask : mask.testBit vertex.val <;>
    simp [Nat.testBit_or, Nat.testBit_mod_two_pow]

theorem maskTransport_edge_extension_new_new
    (parent : Graph) (mask : Nat) :
    edge (extensionGraph parent mask) parent.length parent.length = false := by
  simp only [edge]
  rw [extensionGraph_getD_new]
  simp [Nat.testBit_mod_two_pow]

/-! ## Lifting a parent isomorphism across one-vertex extension -/

/--
Extending the parent permutation by the identity on the new vertex gives an
isomorphism between the source extension and the extension by the transported
mask.
-/
def graphIsoFin_extensionGraph_transportedMask
    {parent representative : Graph}
    (isomorphism : GraphIsoFin parent representative) (mask : Nat) :
    GraphIsoFin
      (extensionGraph parent mask)
      (extensionGraph representative (transportedMask isomorphism mask)) := by
  refine
    { order := isomorphism.order + 1
      sourceOrder := by
        rw [extensionGraph_length, isomorphism.sourceOrder]
      targetOrder := by
        rw [extensionGraph_length, isomorphism.targetOrder]
      permutation := isomorphism.permutation.extendFixed
      map_edge := ?_ }
  intro left right
  refine Fin.lastCases ?_ (fun leftOld => ?_) left
  · refine Fin.lastCases ?_ (fun rightOld => ?_) right
    · have hsource := maskTransport_edge_extension_new_new parent mask
      have htarget := maskTransport_edge_extension_new_new representative
        (transportedMask isomorphism mask)
      simpa [isomorphism.sourceOrder, isomorphism.targetOrder] using
        hsource.trans htarget.symm
    · let sourceOld : Fin parent.length :=
        Fin.cast isomorphism.sourceOrder.symm rightOld
      let targetOld : Fin representative.length :=
        Fin.cast isomorphism.targetOrder.symm
          (isomorphism.permutation rightOld)
      have hsource := maskTransport_edge_extension_new_old
        parent mask sourceOld
      have htarget := maskTransport_edge_extension_new_old
        representative (transportedMask isomorphism mask) targetOld
      calc
        edge (extensionGraph parent mask) (Fin.last isomorphism.order).val
            (Fin.castSucc rightOld).val = mask.testBit rightOld.val := by
          simpa [sourceOld, isomorphism.sourceOrder] using hsource
        _ = (transportedMask isomorphism mask).testBit
              (isomorphism.permutation rightOld).val :=
          (transportedMask_testBit_image isomorphism mask rightOld).symm
        _ = edge
              (extensionGraph representative
                (transportedMask isomorphism mask))
              (isomorphism.permutation.extendFixed
                (Fin.last isomorphism.order)).val
              (isomorphism.permutation.extendFixed
                (Fin.castSucc rightOld)).val := by
          simpa [targetOld, isomorphism.targetOrder] using htarget.symm
  · refine Fin.lastCases ?_ (fun rightOld => ?_) right
    · let sourceOld : Fin parent.length :=
        Fin.cast isomorphism.sourceOrder.symm leftOld
      let targetOld : Fin representative.length :=
        Fin.cast isomorphism.targetOrder.symm
          (isomorphism.permutation leftOld)
      have hsource := maskTransport_edge_extension_old_new
        parent mask sourceOld
      have htarget := maskTransport_edge_extension_old_new
        representative (transportedMask isomorphism mask) targetOld
      calc
        edge (extensionGraph parent mask) (Fin.castSucc leftOld).val
            (Fin.last isomorphism.order).val = mask.testBit leftOld.val := by
          simpa [sourceOld, isomorphism.sourceOrder] using hsource
        _ = (transportedMask isomorphism mask).testBit
              (isomorphism.permutation leftOld).val :=
          (transportedMask_testBit_image isomorphism mask leftOld).symm
        _ = edge
              (extensionGraph representative
                (transportedMask isomorphism mask))
              (isomorphism.permutation.extendFixed
                (Fin.castSucc leftOld)).val
              (isomorphism.permutation.extendFixed
                (Fin.last isomorphism.order)).val := by
          simpa [targetOld, isomorphism.targetOrder] using htarget.symm
    · let sourceLeft : Fin parent.length :=
        Fin.cast isomorphism.sourceOrder.symm leftOld
      let sourceRight : Fin parent.length :=
        Fin.cast isomorphism.sourceOrder.symm rightOld
      let targetLeft : Fin representative.length :=
        Fin.cast isomorphism.targetOrder.symm
          (isomorphism.permutation leftOld)
      let targetRight : Fin representative.length :=
        Fin.cast isomorphism.targetOrder.symm
          (isomorphism.permutation rightOld)
      have hsource := maskTransport_edge_extension_old_old
        parent mask sourceLeft sourceRight
      have htarget := maskTransport_edge_extension_old_old
        representative (transportedMask isomorphism mask)
        targetLeft targetRight
      calc
        edge (extensionGraph parent mask) (Fin.castSucc leftOld).val
            (Fin.castSucc rightOld).val =
            edge parent leftOld.val rightOld.val := by
          simpa [sourceLeft, sourceRight] using hsource
        _ = edge representative
              (isomorphism.permutation leftOld).val
              (isomorphism.permutation rightOld).val :=
          isomorphism.map_edge leftOld rightOld
        _ = edge
              (extensionGraph representative
                (transportedMask isomorphism mask))
              (isomorphism.permutation.extendFixed
                (Fin.castSucc leftOld)).val
              (isomorphism.permutation.extendFixed
                (Fin.castSucc rightOld)).val := by
          simpa [targetLeft, targetRight] using htarget.symm

/-- Propositional wrapper of the lifted extension isomorphism. -/
theorem graphIsomorphicFin_extensionGraph_transportedMask
    {parent representative : Graph}
    (isomorphism : GraphIsoFin parent representative) (mask : Nat) :
    GraphIsomorphicFin
      (extensionGraph parent mask)
      (extensionGraph representative (transportedMask isomorphism mask)) :=
  ⟨graphIsoFin_extensionGraph_transportedMask isomorphism mask⟩

end LRATCatcher.Tests.R35
