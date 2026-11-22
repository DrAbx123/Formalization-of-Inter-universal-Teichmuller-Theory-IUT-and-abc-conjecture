import tmp.sheaf.xif.paper.S2315GaloisImageIsoActual
import tmp.sheaf.xif.paper.S2310GaloisIsoActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2319KernelQuotIsoActual

open LeanFormal.IUT.XiFPaper.S2315GaloisImageIsoActual
open LeanFormal.IUT.XiFPaper.S2310GaloisIsoActual
open LeanFormal.IUT.XiFPaper.S2304GaloisGroupIsoActual
open LeanFormal.IUT.XiFPaper.S2301DegreeEqOrderActual
open LeanFormal.IUT.XiFPaper.S2289QE5DegreeActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual

/-- Since the root kernel is trivial, the root quotient is the polynomial
Galois group itself. -/
noncomputable def S2319RootQuotientEquiv :
    S2304Gal ⧸ S2315RootKernel ≃* S2304Gal :=
  (QuotientGroup.quotientMulEquivOfEq S2315RootKernel_eq_bot).trans
    QuotientGroup.quotientBot

/-- Exact first missing, in the equivalent domain-comparison form: the
polynomial Galois group is isomorphic to the matrix quotient. -/
def S2319GalIsoMatrixQuotRequired
    (b : S1725TorsionBasis S1987Five) : Prop :=
  Nonempty (S2304Gal ≃* (S2315GalF' ⧸ S2315MatrixKernel b))

/-- Equivalence with the S2315 kernel-quotient target. -/
theorem S2319GalIsoMatrixQuotRequired_iff_kernelQuot
    (b : S1725TorsionBasis S1987Five) :
    S2319GalIsoMatrixQuotRequired b ↔
      S2315KernelQuotientIsoRequired b := by
  constructor
  · rintro ⟨e⟩
    exact ⟨S2319RootQuotientEquiv.trans e⟩
  · rintro ⟨e⟩
    exact ⟨S2319RootQuotientEquiv.symm.trans e⟩

/-- From the domain-comparison iso, construct the S2310 Galois-group/image
iso. -/
theorem S2319S2310Iso_of_galIsoMatrixQuot
    (b : S1725TorsionBasis S1987Five)
    (e : S2304Gal ≃* (S2315GalF' ⧸ S2315MatrixKernel b)) :
    S2310GaloisImageIsoRequired
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range := by
  refine ⟨⟨e.trans (S2315MatrixQuotEquiv b)⟩⟩

/-- Exact first missing in its final domain-comparison form. -/
def S2319ExactFirstMissing
    (b : S1725TorsionBasis S1987Five) : Prop :=
  S2319GalIsoMatrixQuotRequired b

end LeanFormal.IUT.XiFPaper.S2319KernelQuotIsoActual

end
