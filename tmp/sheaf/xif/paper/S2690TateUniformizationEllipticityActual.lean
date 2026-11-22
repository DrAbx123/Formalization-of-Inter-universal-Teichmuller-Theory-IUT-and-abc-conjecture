import LeanFormal.IUT.Foundations.Geometry.TateUniformizationContract
import LeanFormal.IUT.Foundations.Geometry.TateCurvePointMap
import LeanFormal.IUT.Foundations.Geometry.TateCurveArithmetic
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import tmp.sheaf.xif.paper.S2682CurveIndexedTateSplitActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Foundations.TatePointMap
open scoped Valued
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2690TateUniformizationEllipticityActual

variable {K : Type} [Field K] [NumberField K]
variable (place : NumberField.FinitePlace K)
variable (parameter : FinitePlaceQCandidate place)

/-- The canonical q-series is actually elliptic at every finite-place
q-candidate. This completely discharges the canonicalIsElliptic field of
CurveIndexedTateUniformization. -/
theorem S2690_canonicalIsElliptic :
    (TateCurve.weierstrassCurve
      (NumberFieldFinitePlace.Completion place) parameter.q).IsElliptic := by
  exact LeanFormal.IUT.Foundations.TatePointMap.tateWeierstrassCurve_isElliptic_of_norm
    parameter.q_ne_zero
    (LeanFormal.IUT.ArithmeticQPilotLogVolume.qNorm_lt_one parameter)

/-- The exact residual contract after discharging the ellipticity field. -/
structure S2690Residual
    {F : Type} [Field F] [NumberField F]
    (X : PuncturedEllipticCurve F)
    (place : NumberField.FinitePlace F)
    (parameter : FinitePlaceQCandidate place) where
  coordinateChange : WeierstrassCurve.VariableChange
    (NumberFieldFinitePlace.Completion place)
  realizesCurve :
    coordinateChange •
        TateCurve.weierstrassCurve
          (NumberFieldFinitePlace.Completion place) parameter.q =
      (X.baseChange (NumberFieldFinitePlace.Completion place)).curve
  analytic : CurveIndexedTateUniformizationAnalytic X place parameter

/-- The full curve-indexed Tate uniformization has a point iff the residual
contract does.  The forward direction forgets the ellipticity field; the
backward direction fills it with S2690_canonicalIsElliptic.  This is the exact
minimal remaining target: coordinate change, curve realization, and the
analytic point uniformization. -/
theorem S2690_nonempty_iff_residual
    {F : Type} [Field F] [NumberField F]
    (X : PuncturedEllipticCurve F)
    (place : NumberField.FinitePlace F)
    (parameter : FinitePlaceQCandidate place) :
    Nonempty (CurveIndexedTateUniformization X place parameter) ↔
      Nonempty (S2690Residual X place parameter) := by
  constructor
  · rintro ⟨u⟩
    refine ⟨{
      coordinateChange := u.coordinateChange
      realizesCurve := u.realizesCurve
      analytic := {
        pointUniformization := u.pointUniformization
        pointUniformization_galoisEquivariant :=
          u.pointUniformization_galoisEquivariant } }⟩
  · rintro ⟨r⟩
    refine ⟨{
      canonicalIsElliptic := S2690_canonicalIsElliptic place parameter
      coordinateChange := r.coordinateChange
      realizesCurve := r.realizesCurve
      pointUniformization := r.analytic.pointUniformization
      pointUniformization_galoisEquivariant :=
        r.analytic.pointUniformization_galoisEquivariant }⟩

#check S2690_canonicalIsElliptic
#print axioms S2690_canonicalIsElliptic
#check S2690Residual
#check S2690_nonempty_iff_residual
#print axioms S2690_nonempty_iff_residual
end LeanFormal.IUT.XiFPaper.S2690TateUniformizationEllipticityActual
end
