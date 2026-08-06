import LRATCatcher.Tests.R35CatalogExtensionProperties

/-!
  Canonical round-trip laws for the materialized one-vertex extension.

  Decomposing `extensionGraph parent mask` at its final vertex recovers the
  original parent whenever that parent is well formed, and recovers the mask
  whenever the mask is already in the canonical range.
-/

namespace LRATCatcher.Tests.R35

open LRATCatcher.Ramsey

/-- Decomposing a materialized extension recovers its well-formed parent. -/
@[simp] theorem initialParent_extensionGraph
    (parent : Graph) (mask : Nat)
    (hparent : wellFormedGraph parent.length parent = true) :
    initialParent (extensionGraph parent mask) parent.length = parent := by
  apply List.ext_getElem
  · exact initialParent_length
      (extensionGraph parent mask) parent.length (by simp)
  · intro vertex hextension hparentVertex
    rw [List.getElem_eq_getD 0, List.getElem_eq_getD 0]
    rw [initialParent_getD
      (extensionGraph parent mask) parent.length vertex hparentVertex]
    rw [extensionGraph_getD_old parent mask vertex hparentVertex]
    have hrow : parent.getD vertex 0 < 2 ^ parent.length :=
      wellFormedGraph_row_bound
        parent parent.length vertex hparent hparentVertex
    apply Nat.eq_of_testBit_eq
    intro bit
    by_cases hbit : bit < parent.length
    · have hne : parent.length ≠ bit := by omega
      split <;>
        simp [Nat.testBit_mod_two_pow, Nat.testBit_or, hbit, hne]
    · have hpow : parent.getD vertex 0 < 2 ^ bit :=
        Nat.lt_of_lt_of_le hrow
          (Nat.pow_le_pow_right (by decide) (by omega))
      have hzero : (parent.getD vertex 0).testBit bit = false :=
        Nat.testBit_lt_two_pow hpow
      simp only [Nat.testBit_mod_two_pow, hbit, decide_false,
        Bool.false_and]
      simpa only [List.getD_eq_getElem?_getD] using hzero.symm

/-- The final row of a materialized extension is its canonical mask. -/
@[simp] theorem finalVertexMask_extensionGraph
    (parent : Graph) (mask : Nat)
    (hmask : mask < 2 ^ parent.length) :
    finalVertexMask (extensionGraph parent mask) parent.length = mask := by
  unfold finalVertexMask
  rw [extensionGraph_getD_new, Nat.mod_eq_of_lt hmask]

/--
If the materialized graph is valid, the canonical decomposition theorem
certifies the original pair `(parent, mask)` as a valid extension.
-/
theorem validExtension_of_extensionGraph_valid
    (parent : Graph) (mask : Nat)
    (hparent : wellFormedGraph parent.length parent = true)
    (hmask : mask < 2 ^ parent.length)
    (hvalid : validGraph (extensionGraph parent mask) = true) :
    validExtension parent mask = true := by
  have hwellFormed :
      wellFormedGraph (parent.length + 1) (extensionGraph parent mask) = true :=
    extensionGraph_wellFormed
      parent parent.length mask hparent hmask
  have hdecomposed := finalVertex_validExtension
    (extensionGraph parent mask) parent.length hwellFormed hvalid
  simpa [initialParent_extensionGraph parent mask hparent,
    finalVertexMask_extensionGraph parent mask hmask] using hdecomposed

end LRATCatcher.Tests.R35
