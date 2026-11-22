import LeanFormal.IUT.Foundations.Geometry.TateUniformizationContract
import tmp.sheaf.xif.paper.S2690TateUniformizationEllipticityActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2690TateUniformizationEllipticityActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2691TateUniformizationTransferActual

variable {F : Type} [Field F] [NumberField F]
variable {X X' : PuncturedEllipticCurve F}
variable {place place' : NumberField.FinitePlace F}
variable {parameter : FinitePlaceQCandidate place}
variable {parameter' : FinitePlaceQCandidate place'}

/-- A coordinate half transports across equal curve, equal place, and equal
q-value.  The coordinate contract sees only the q-value. -/
noncomputable def S2691_coordinate_transfer
    (hX : X = X') (hplace : place = place') (hq : HEq parameter.q parameter'.q)
    (c : CurveIndexedTateUniformizationCoordinate X place parameter) :
    CurveIndexedTateUniformizationCoordinate X' place' parameter' := by
  subst hX
  subst hplace
  obtain ⟨q', hq0', hval'⟩ := parameter'
  have hq' : parameter.q = q' := eq_of_heq hq
  subst q'
  exact c

/-- The analytic half transports across equal curve, equal place, and equal
q-value.  The point uniformization sees only the q-value and the local curve. -/
noncomputable def S2691_analytic_transfer
    (hX : X = X') (hplace : place = place') (hq : HEq parameter.q parameter'.q)
    (a : CurveIndexedTateUniformizationAnalytic X place parameter) :
    CurveIndexedTateUniformizationAnalytic X' place' parameter' := by
  subst hX
  subst hplace
  obtain ⟨q', hq0', hval'⟩ := parameter'
  have hq' : parameter.q = q' := eq_of_heq hq
  subst q'
  exact a

/-- The residual contract transports across equal curve, equal place, and equal
q-value. -/
noncomputable def S2691_residual_transfer
    (hX : X = X') (hplace : place = place') (hq : HEq parameter.q parameter'.q)
    (r : S2690Residual X place parameter) :
    S2690Residual X' place' parameter' := by
  subst hX
  subst hplace
  obtain ⟨q', hq0', hval'⟩ := parameter'
  have hq' : parameter.q = q' := eq_of_heq hq
  subst q'
  exact r

#check S2691_coordinate_transfer
#check S2691_analytic_transfer
#check S2691_residual_transfer
#print axioms S2691_coordinate_transfer
#print axioms S2691_analytic_transfer
#print axioms S2691_residual_transfer
end LeanFormal.IUT.XiFPaper.S2691TateUniformizationTransferActual
end
