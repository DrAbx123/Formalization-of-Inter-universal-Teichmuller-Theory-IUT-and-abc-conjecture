import tmp.sheaf.xif.paper.S2310GaloisIsoActual
import Mathlib.GroupTheory.QuotientGroup.Basic
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import tmp.sheaf.xif.paper.S1725SourceTorsionFPrimeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2315GaloisImageIsoActual

open LeanFormal.IUT.XiFPaper.S2310GaloisIsoActual
open LeanFormal.IUT.XiFPaper.S2304GaloisGroupIsoActual
open LeanFormal.IUT.XiFPaper.S2301DegreeEqOrderActual
open LeanFormal.IUT.XiFPaper.S2289QE5DegreeActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open Polynomial

/-- The absolute Galois group of F' used by the matrix representation. -/
abbrev S2315GalF' : Type :=
  AlgebraicClosure S1720Field ≃ₐ[S1720Field] AlgebraicClosure S1720Field

/-- The kernel of the faithful root action on psi5. -/
noncomputable def S2315RootKernel : Subgroup S2304Gal :=
  S2310RootAction.ker

/-- The kernel of the actual mod-5 matrix representation at a basis. -/
noncomputable def S2315MatrixKernel
    (b : S1725TorsionBasis S1987Five) : Subgroup S2315GalF' :=
  (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).ker

instance S2315RootKernel_normal : S2315RootKernel.Normal := by
  unfold S2315RootKernel
  infer_instance

instance S2315MatrixKernel_normal (b : S1725TorsionBasis S1987Five) :
    (S2315MatrixKernel b).Normal := by
  unfold S2315MatrixKernel
  infer_instance

/-- The root kernel is trivial because the root action is faithful. -/
theorem S2315RootKernel_eq_bot : S2315RootKernel = ⊥ := by
  unfold S2315RootKernel
  rw [MonoidHom.ker_eq_bot_iff]
  exact S2310RootAction_injective

/-- First isomorphism theorem for the root action. -/
noncomputable def S2315RootQuotEquiv :
    S2304Gal ⧸ S2315RootKernel ≃* S2310RootActionImage :=
  QuotientGroup.quotientKerEquivRange S2310RootAction

/-- First isomorphism theorem for the matrix representation. -/
noncomputable def S2315MatrixQuotEquiv
    (b : S1725TorsionBasis S1987Five) :
    S2315GalF' ⧸ S2315MatrixKernel b ≃*
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range :=
  QuotientGroup.quotientKerEquivRange
    (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b)

/-- Exact first missing: the root-action image is isomorphic to the matrix
range, equivalently the two kernel quotients are isomorphic. -/
def S2315KernelQuotientIsoRequired
    (b : S1725TorsionBasis S1987Five) : Prop :=
  Nonempty ((S2304Gal ⧸ S2315RootKernel) ≃*
    (S2315GalF' ⧸ S2315MatrixKernel b))

/-- Conditional root-image/matrix-range isomorphism from the kernel quotient
isomorphism and the two first-isomorphism equivalences. -/
theorem S2315RootImageIsoMatrixRange_of_kernelQuot
    (b : S1725TorsionBasis S1987Five)
    (e : (S2304Gal ⧸ S2315RootKernel) ≃*
      (S2315GalF' ⧸ S2315MatrixKernel b)) :
    Nonempty (S2310RootActionImage ≃*
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range) := 
  ⟨(S2315RootQuotEquiv.symm.trans e).trans (S2315MatrixQuotEquiv b)⟩

end LeanFormal.IUT.XiFPaper.S2315GaloisImageIsoActual

end
