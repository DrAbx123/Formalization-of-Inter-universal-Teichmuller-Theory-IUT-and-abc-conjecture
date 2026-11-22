import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.ArithmeticQPilotLogVolume
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2710PerPlaceLogEqActual

universe u

/-- For `x > 1` and `n > 0`, the absolute log of `x⁻¹ⁿ` is `n log x`. -/
theorem S2710_abs_log_inv_pow {x : Real} (hx : 1 < x) (n : Nat) (hn : 0 < n) :
    |Real.log (x⁻¹ ^ n)| = (n : Real) * Real.log x := by
  rw [Real.log_pow, Real.log_inv]
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hnpos : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hneg : (n : Real) * -Real.log x < 0 := by nlinarith
  rw [abs_of_neg hneg]
  ring

/-- The per-place log identity for a q candidate, reduced to the residue-norm
equality `residueNormBase place = residueCharacteristic b.1` and order
agreement. -/
theorem S2710_localLog_eq_abs_log_proxy
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    (P : SourcePlaceSelection A) (b : Bad P)
    {K : Type u} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K)
    (q : FinitePlaceQCandidate place)
    (horder : q.order = (badPlaceQCandidate P b).order)
    (hres : residueNormBase place =
      (residueCharacteristic b.1 : ℝ)) :
    localLogMagnitude q = |Real.log (badPlaceQProxy P b)| := by
  rw [localLogMagnitude_eq_order_mul_log, hres, horder]
  rw [show badPlaceQProxy P b =
      ((residueCharacteristic b.1 : Nat) : Real)⁻¹ ^
        (badPlaceQCandidate P b).order from rfl]
  rw [S2710_abs_log_inv_pow]
  · exact_mod_cast (residueCharacteristic_prime b.1).one_lt
  · exact badPlaceQCandidate_order_pos P b

#check S2710_abs_log_inv_pow
#check S2710_localLog_eq_abs_log_proxy
#print axioms S2710_localLog_eq_abs_log_proxy

end LeanFormal.IUT.XiFPaper.S2710PerPlaceLogEqActual
end
