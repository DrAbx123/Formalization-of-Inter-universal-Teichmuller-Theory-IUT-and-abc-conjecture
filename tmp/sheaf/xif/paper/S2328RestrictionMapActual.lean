import tmp.sheaf.xif.paper.S2325DomainComparisonActual
import tmp.sheaf.xif.paper.S2253LinearDisjointActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2328RestrictionMapActual

open LeanFormal.IUT.XiFPaper.S2325DomainComparisonActual
open LeanFormal.IUT.XiFPaper.S2319KernelQuotIsoActual
open LeanFormal.IUT.XiFPaper.S2315GaloisImageIsoActual
open LeanFormal.IUT.XiFPaper.S2310GaloisIsoActual
open LeanFormal.IUT.XiFPaper.S2304GaloisGroupIsoActual
open LeanFormal.IUT.XiFPaper.S2253LinearDisjointActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-- The linear-disjointness prerequisite for the domain comparison. -/
def S2328LinearDisjointnessRequired : Prop :=
  s2253IntersectionIsBot

/-- Constructor for the exact restriction data from explicit map, kernel,
surjectivity and the linear-disjointness prerequisite. -/
noncomputable def S2328RestrictionData_of
    (b : S1725TorsionBasis S1987Five)
    (restrict : S2315GalF' →* S2304Gal)
    (ker_eq : restrict.ker = S2315MatrixKernel b)
    (surjective : Function.Surjective restrict)
    (linearDisjoint : S2328LinearDisjointnessRequired) :
    S2325RestrictionData b where
  restrict := restrict
  ker_eq := ker_eq
  surjective := surjective
  linearDisjoint := linearDisjoint

/-- Exact first missing: an actual restriction map with the stated kernel and
surjectivity, plus the linear-disjointness prerequisite. -/
def S2328ExactFirstMissing
    (b : S1725TorsionBasis S1987Five) : Prop :=
  S2325RestrictionDataRequired b ∧ S2328LinearDisjointnessRequired

/-- Conditional S2310 iso from the restriction data half. -/
theorem S2328S2310Iso_of_restrictionData
    (b : S1725TorsionBasis S1987Five)
    (D : S2325RestrictionData b) :
    S2310GaloisImageIsoRequired
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range :=
  S2325S2310Iso_of_restriction b D

/-- Conditional S2310 iso from the exact conjunction. -/
theorem S2328S2310Iso_of_exactFirstMissing
    (b : S1725TorsionBasis S1987Five)
    (h : S2328ExactFirstMissing b) :
    S2310GaloisImageIsoRequired
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range := by
  rcases h with ⟨⟨D⟩, _⟩
  exact S2328S2310Iso_of_restrictionData b D

end LeanFormal.IUT.XiFPaper.S2328RestrictionMapActual

end
