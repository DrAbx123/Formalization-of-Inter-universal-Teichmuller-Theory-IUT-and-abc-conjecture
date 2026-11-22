import LeanFormal.IUT.IUTII.Theta.FiniteThetaPacket
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S634QParameterThetaNormalizationActual

open LeanFormal.IUT
open scoped BigOperators

universe u
variable {l : PrimeGeFive}

/-- Corrected theta value built from the q-parameter q[1u]:
q[1u]^(j^2/(2l)) = q[2u]^(j^2). -/
noncomputable def qParameterThetaValue (q : Real) (j : Int) : Real :=
  Real.rpow q ((gaussExponent j : Real) / (2 * (l.value : Real)))

theorem qParameterThetaValue_pos {q : Real} (hq : 0 < q) (j : Int) :
    0 < qParameterThetaValue (l := l) q j :=
  Real.rpow_pos_of_pos hq _

theorem log_qParameterThetaValue {q : Real} (hq : 0 < q) (j : Int) :
    Real.log (qParameterThetaValue (l := l) q j) =
      ((gaussExponent j : Real) / (2 * (l.value : Real))) * Real.log q :=
  Real.log_rpow hq _

/-- Corrected signed theta value: -log(q[1u]^(j^2/(2l))). -/
noncomputable def qParameterSignedThetaValue (q : Real) (j : Int) : Real :=
  -Real.log (qParameterThetaValue (l := l) q j)

theorem qParameterSignedThetaValue_eq {q : Real} (hq : 0 < q) (j : Int) :
    qParameterSignedThetaValue (l := l) q j =
      ((gaussExponent j : Real) / (2 * (l.value : Real))) * (-Real.log q) :=
  rw [qParameterSignedThetaValue, log_qParameterThetaValue (l := l) hq j]
  ring

/-- The corrected finite signed theta average. -/
noncomputable def qParameterSignedAverage (q : Real) : Real :=
  (∑ j : SignedLabel l.value, qParameterSignedThetaValue (l := l) q j.1) /
    (Fintype.card (SignedLabel l.value) : Real)

abbrev qParameterThetaCard : Nat := Fintype.card (SignedLabel l.value)

noncomputable def qParameterExponentSum : Real :=
  ∑ j : SignedLabel l.value, (gaussExponent j.1 : Real)

theorem qParameterSignedAverage_eq {q : Real} (hq : 0 < q) :
    qParameterSignedAverage (l := l) q =
      (qParameterExponentSum (l := l) /
        (2 * (l.value : Real) * (qParameterThetaCard (l := l) : Real))) *
        (-Real.log q) := by
  unfold qParameterSignedAverage qParameterSignedThetaValue qParameterExponentSum
  rw [Finset.sum_congr rfl (fun j _ => qParameterSignedThetaValue_eq (l := l) hq j.1)]
  rw [← Finset.sum_mul]
  rw [Finset.sum_div]
  rw [← Finset.sum_mul]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- The coefficient multiplying -log q in the corrected average. -/
noncomputable def qParameterAverageCoefficient : Real :=
  qParameterExponentSum (l := l) /
    (2 * (l.value : Real) * (qParameterThetaCard (l := l) : Real))

theorem qParameterAverageCoefficient_nonneg :
    0 ≤ qParameterAverageCoefficient (l := l) :=
  div_nonneg (Finset.sum_nonneg (fun j _ => by
    exact_mod_cast gaussExponent_nonneg j.1)) (by positivity)

/-- Corrected comparison with the q-pilot magnitude, conditional on the exact
normalization coefficient bound. -/
theorem qParameterSignedAverage_le_qPilotMagnitude
    {q : Real} (hq : 0 < q) (hq1 : q ≤ 1)
    (hcoef : qParameterAverageCoefficient (l := l) ≤ 1) :
    qParameterSignedAverage (l := l) q ≤ -Real.log q := by
  have hlog : 0 ≤ -Real.log q := by
    rw [neg_nonneg]
    exact Real.log_nonpos (le_of_lt hq) hq1
  rw [qParameterSignedAverage_eq (l := l) hq]
  have hcoef' := mul_le_mul_of_nonneg_right hcoef hlog
  simpa [qParameterAverageCoefficient, mul_assoc] using hcoef'

/-- Exact normalization gap: coefficient ≤ 1. -/
def QParameterNormalizationCoefficientLeOne : Prop :=
  qParameterAverageCoefficient (l := l) ≤ 1

end LeanFormal.IUT.XiFPaper.S634QParameterThetaNormalizationActual

end
