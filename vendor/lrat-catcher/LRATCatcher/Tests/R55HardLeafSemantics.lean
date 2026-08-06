import LRATCatcher.Tests.R55HardLeafBridge
import LRATCatcher.Tests.R55MinLeafSemantics

/-!
  Conditional end-to-end semantics of the certified hard W5 leaf.

  The complete external formula is checked against an exact decomposition.
  The terminal theorem keeps all search-strengthening blocks explicit:
  rooted degree counters, exact internal regularity, signature sorting, and
  the residual W5 signature symmetry break.  Their future soundness/WLOG
  proofs can therefore be attached without changing the LRAT boundary.
-/

namespace LRATCatcher.Tests.R55.HardLeaf

open Std.Sat
open LRATCatcher.Ramsey
open CanonicalUnits
open TypedUnits

def rootedDegreeCNF : CNF Nat :=
  { clauses := rootedDegreeClauses }

def internalRegularityCNF : CNF Nat :=
  { clauses := internalRegularityClauses }

def signatureLexCNF : CNF Nat :=
  { clauses := signatureLexClauses }

def w5SymmetryCNF : CNF Nat :=
  { clauses := w5SymmetryClauses }

def hardD20C10T312W5Decomposition : CNF Nat :=
  MinLeaf.pythonInterleavedRamseyEncode 43 5 ++
    rootedDegreeCNF ++
    internalRegularityCNF ++
    signatureLexCNF ++
    w5SymmetryCNF ++
    MinLeaf.unitsCNF canonicalRootUnits ++
    MinLeaf.unitsCNF canonicalAnchorUnits ++
    MinLeaf.unitsCNF
      (fixedAnchorTypeUnits (orderTenCatalogueType 312))

/-- Exact semantic residue of the hard W5 certificate.  Each field concerns
the full assignment, including the dedicated auxiliary-variable interval. -/
structure StrengtheningBlocksSatisfied (assignment : Nat -> Bool) : Prop where
  rootedDegree : CNF.eval assignment rootedDegreeCNF = true
  internalRegularity : CNF.eval assignment internalRegularityCNF = true
  signatureLex : CNF.eval assignment signatureLexCNF = true
  w5Symmetry : CNF.eval assignment w5SymmetryCNF = true

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Computational equality pins down every one of the 2,049,737 clauses,
including all block boundaries and catalogue index 312. -/
theorem hardD20C10T312W5Formula_eq_decomposition :
    hardD20C10T312W5Formula = hardD20C10T312W5Decomposition := by
  apply CNF.Internal.ext_iff.mpr
  native_decide

/-- Sound conditional use of the hard W5 LRAT leaf.  No regularity or
symmetry assumption is hidden in Ramsey-freeness. -/
theorem no_t312_hard_assignment
    (assignment : Nat -> Bool)
    (hfree : isRamseyFree 43 5 5 assignment)
    (canonical : CanonicalD20C10Units assignment)
    (type312 :
      TypeUnitsSatisfied assignment (orderTenCatalogueType 312))
    (blocks : StrengtheningBlocksSatisfied assignment) : False := by
  have hsat : CNF.eval assignment hardD20C10T312W5Formula = true := by
    rw [hardD20C10T312W5Formula_eq_decomposition]
    have hramsey :=
      MinLeaf.pythonInterleavedRamseyEncode_sat assignment hfree
    have hroot :=
      (MinLeaf.unitsCNF_sat_iff assignment canonicalRootUnits).mpr
        canonical.root
    have hanchor :=
      (MinLeaf.unitsCNF_sat_iff assignment canonicalAnchorUnits).mpr
        canonical.anchor
    have htype :=
      (MinLeaf.unitsCNF_sat_iff assignment
        (fixedAnchorTypeUnits (orderTenCatalogueType 312))).mpr type312
    simp [hardD20C10T312W5Decomposition, hramsey,
      blocks.rootedDegree, blocks.internalRegularity,
      blocks.signatureLex, blocks.w5Symmetry, hroot, hanchor, htype]
  have hfalse := hardD20C10T312W5Formula_unsat assignment
  rw [hsat] at hfalse
  contradiction

#print axioms hardD20C10T312W5Formula_eq_decomposition
#print axioms no_t312_hard_assignment

end LRATCatcher.Tests.R55.HardLeaf
