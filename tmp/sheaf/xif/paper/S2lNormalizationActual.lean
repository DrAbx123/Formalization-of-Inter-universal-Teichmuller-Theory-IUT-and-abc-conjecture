import LeanFormal.IUT.Foundations.Arithmetic.PrimeLabels
import LeanFormal.IUT.Foundations.Theta.GaussianKernel
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open LeanFormal.IUT
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2lNormalizationActual

noncomputable def paperThetaValueFromQParameter
    (l : PrimeGeFive) (q : Real) (j : Int) : Real :=
  Real.rpow q (((gaussExponent j).toNat : Real) / (2 * (l.1 : Real)))

theorem paperThetaValueFromQParameter_pos
    {l : PrimeGeFive} {q : Real} (hq : 0 < q) (j : Int) :
    0 < paperThetaValueFromQParameter l q j := by
  unfold paperThetaValueFromQParameter
  exact Real.rpow_pos_of_pos hq _

theorem log_paperThetaValueFromQParameter
    {l : PrimeGeFive} {q : Real} (hq : 0 < q) (j : Int) :
    Real.log (paperThetaValueFromQParameter l q j) =
      ((gaussExponent j).toNat : Real) / (2 * l.1) * Real.log q := by
  unfold paperThetaValueFromQParameter
  rw [Real.log_rpow hq]
  ring

theorem paperThetaValueFromQParameter_eq_root
    {l : PrimeGeFive} {q r : Real} (hr : 0 < r) (hq : q = r ^ (2 * l.1))
    (j : Int) :
    paperThetaValueFromQParameter l q j = realThetaValue r j := by
  unfold paperThetaValueFromQParameter realThetaValue
  rw [hq]
  rw [← Real.rpow_natCast (r ^ (2 * l.1)) ((gaussExponent j).toNat)]
  rw [← Real.rpow_natCast r ((2 * l.1) * (gaussExponent j).toNat)]
  rw [Real.rpow_mul (le_of_lt hr)]
  have hdiv : ((2 * l.1 : Nat) : Real) *
      (((gaussExponent j).toNat : Real) / (2 * l.1)) =
      (gaussExponent j).toNat := by
    field_simp [Nat.cast_ne_zero.mpr l.prime.ne_zero]
    ring
  rw [hdiv]

end LeanFormal.IUT.XiFPaper.S2lNormalizationActual
end