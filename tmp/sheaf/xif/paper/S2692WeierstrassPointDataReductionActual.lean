import LeanFormal.IUT.Foundations.Geometry.TateUniformizationPointMap
import LeanFormal.IUT.Foundations.Geometry.TateWeierstrassPointEquation
import tmp.sheaf.xif.paper.S2690TateUniformizationEllipticityActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.TateCurve
open LeanFormal.IUT.XiFPaper.S2690TateUniformizationEllipticityActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2692WeierstrassPointDataReductionActual

variable {K : Type} [Field K] [NumberField K]
variable (place : NumberField.FinitePlace K)
variable (parameter : FinitePlaceQCandidate place)

/-- The point-nonsingularity data for the canonical q-series at a finite-place
q-candidate is *exactly* the classical analytic point equation, with no extra
condition: Mathlib's elliptic-curve nonsingularity equivalence removes the
partial-derivative conditions.  This is the minimal remaining analytic target. -/
theorem S2692_pointData_iff_equation :
    letI : (TateCurve.weierstrassCurve
        (NumberFieldFinitePlace.Completion place) parameter.q).IsElliptic :=
      S2690_canonicalIsElliptic place parameter
    TateWeierstrassPointData parameter.q ↔
      ∀ u : ↥(coordinateParameterDomain parameter.q),
        tateWeierstrassEquation parameter.q (u : NumberFieldFinitePlace.Completion place) := by
  letI : (TateCurve.weierstrassCurve
      (NumberFieldFinitePlace.Completion place) parameter.q).IsElliptic :=
    S2690_canonicalIsElliptic place parameter
  constructor
  · intro hdata u
    exact (WeierstrassCurve.Affine.equation_iff_nonsingular).mpr (hdata u)
  · intro heq u
    exact (WeierstrassCurve.Affine.equation_iff_nonsingular).mp (heq u)

#check S2692_pointData_iff_equation
#print axioms S2692_pointData_iff_equation
end LeanFormal.IUT.XiFPaper.S2692WeierstrassPointDataReductionActual
end
