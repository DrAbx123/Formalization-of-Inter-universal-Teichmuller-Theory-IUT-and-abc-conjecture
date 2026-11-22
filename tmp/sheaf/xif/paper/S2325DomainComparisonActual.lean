import tmp.sheaf.xif.paper.S2319KernelQuotIsoActual
import tmp.sheaf.xif.paper.S2253LinearDisjointActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2325DomainComparisonActual

open LeanFormal.IUT.XiFPaper.S2319KernelQuotIsoActual
open LeanFormal.IUT.XiFPaper.S2315GaloisImageIsoActual
open LeanFormal.IUT.XiFPaper.S2310GaloisIsoActual
open LeanFormal.IUT.XiFPaper.S2304GaloisGroupIsoActual
open LeanFormal.IUT.XiFPaper.S2253LinearDisjointActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual

/-- Exact domain-comparison data: an actual restriction homomorphism from
Gal(F'/F') to Gal(Q(E[5])/Q), whose kernel is the matrix kernel and whose
image is everything; the linear-disjointness prerequisite is recorded. -/
structure S2325RestrictionData
    (b : S1725TorsionBasis S1987Five) where
  restrict : S2315GalF' →* S2304Gal
  ker_eq : restrict.ker = S2315MatrixKernel b
  surjective : Function.Surjective restrict
  linearDisjoint : s2253IntersectionIsBot

/-- Exact first missing: the restriction data (kernel/surjectivity plus the
linear-disjointness prerequisite). -/
def S2325RestrictionDataRequired
    (b : S1725TorsionBasis S1987Five) : Prop :=
  Nonempty (S2325RestrictionData b)

/-- Conditional domain comparison from the restriction data. -/
theorem S2325GalIsoMatrixQuot_of_restriction
    (b : S1725TorsionBasis S1987Five)
    (D : S2325RestrictionData b) :
    S2319GalIsoMatrixQuotRequired b := by
  let e := QuotientGroup.quotientKerEquivOfSurjective D.restrict D.surjective
  refine ⟨e.symm.trans (QuotientGroup.quotientMulEquivOfEq D.ker_eq)⟩

/-- Conditional S2310 Galois/image iso from the restriction data. -/
theorem S2325S2310Iso_of_restriction
    (b : S1725TorsionBasis S1987Five)
    (D : S2325RestrictionData b) :
    S2310GaloisImageIsoRequired
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range :=
  S2319S2310Iso_of_galIsoMatrixQuot b
    ((S2325GalIsoMatrixQuot_of_restriction b D).some)

/-- Exact first missing in its final form. -/
def S2325ExactFirstMissing
    (b : S1725TorsionBasis S1987Five) : Prop :=
  S2325RestrictionDataRequired b

end LeanFormal.IUT.XiFPaper.S2325DomainComparisonActual

end
