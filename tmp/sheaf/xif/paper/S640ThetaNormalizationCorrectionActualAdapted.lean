import tmp.sheaf.xif.paper.ProcessionThetaPacketAverageActual
/-! # S640: CRITICAL 2l normalization correction
`C3.q` is q[1u] (q-parameter), while `realThetaValue q j = q^(j^2)` treats
q as q[2u].  The paper q-parameter theta value is q[1u]^(j^2/(2l)).
On log-scales this is exactly the old log-scale divided by 2l.  This file
constructs the corrected q[1u]-procession and proves the exact division law;
it does not prove any false unnormalized inequality. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S640ThetaNormalizationCorrectionActualAdapted
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
open scoped BigOperators
universe ua uv upi umon ui uL uC uG uX uLabel
variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
/-- Corrected q[1u] theta procession: log-scale is old log-scale / (2l). -/
noncomputable def c3ThetaProcessionQParameter :
    WeightedValues (SignedLabel l.value) := by
  let twoL : Real := (2 * l.value : Nat)
  exact
    { value := fun j => Real.log (C3.thetaPacket.scale j) / twoL
      weight := fun _ => (c3ThetaCard (l := l) : Real)⁻¹
      weightTotal := 1
      weightTotal_pos := by norm_num
      weightTotal_eq_sum := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        have hcard : (c3ThetaCard (l := l) : Real) ≠ 0 := by
          exact_mod_cast (ne_of_gt (c3ThetaCard_pos (l := l)))
        exact (mul_inv_cancel₀ hcard).symm }
theorem c3ThetaProcessionQParameter_value
    (j : SignedLabel l.value) :
    (c3ThetaProcessionQParameter C3).value j =
      Real.log (C3.thetaPacket.scale j) / (2 * l.value : Real) := rfl
/-- The corrected average is exactly the old average divided by 2l. -/
theorem c3ThetaProcessionQParameter_average :
    (c3ThetaProcessionQParameter C3).average =
      (c3ThetaProcession C3).average / (2 * l.value : Real) := by
  unfold c3ThetaProcessionQParameter c3ThetaProcession
  rw [WeightedValues.average, WeightedValues.average]
  simp only
  rw [Finset.sum_div, div_one, div_eq_mul_inv, div_eq_mul_inv]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring
/-- Log-scale formula: the corrected scale is the 1/(2l)-power log. -/
theorem c3ThetaProcessionQParameter_log_eq
    (j : SignedLabel l.value) :
    (c3ThetaProcessionQParameter C3).value j =
      ((gaussExponent j.1).toNat : Real) * Real.log C3.thetaPacket.q /
        (2 * l.value : Real) := by
  rw [c3ThetaProcessionQParameter_value, C3.thetaPacket.log_scale]
/-- Exact missing warning in Lean form: the old procession is the q[2u]-scale,
so using it for q[1u] overcounts by 2l.  This is a Prop, not an inequality proof. -/
def OldProcessionOvercountsByTwoL : Prop :=
  (c3ThetaProcession C3).average =
    (2 * l.value : Real) * (c3ThetaProcessionQParameter C3).average
theorem oldProcessionOvercountsByTwoL :
    OldProcessionOvercountsByTwoL C3 := by
  unfold OldProcessionOvercountsByTwoL
  rw [c3ThetaProcessionQParameter_average]
  have htwo : (2 * (l.value : Real)) ≠ 0 := by positivity
  field_simp [htwo]
  ring_nf
end LeanFormal.IUT.XiFPaper.S640ThetaNormalizationCorrectionActualAdapted
