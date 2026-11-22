/- Route 7.2 local-field instances needed by the direct different bound. -/
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellRamificationInertia
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1LocalFieldInstancesActual

open LeanFormal.IUT.LocalFieldIntegralUnits

variable {p : Nat} [Fact p.Prime]
variable {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L] [IsUltrametricDist L]
  [ProperSpace L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]

/-- The maximal ideal of the integers is prime. -/
instance maximalIdeal_isPrime : (IsLocalRing.maximalIdeal (Integers L)).IsPrime :=
  (IsLocalRing.maximalIdeal.isMaximal (Integers L)).isPrime

/-- L is torsion-free over Z_p (field, char 0). -/
instance noZeroSMulDivisors_field : NoZeroSMulDivisors ℤ_[p] L where
  eq_zero_or_eq_zero_of_smul_eq_zero {c x} h := by
    letI : IsScalarTower ℤ_[p] ℚ_[p] L :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have hinj : Function.Injective (algebraMap ℤ_[p] L) := by
      intro a b hab
      have hq : algebraMap ℤ_[p] ℚ_[p] a = algebraMap ℤ_[p] ℚ_[p] b := by
        apply (algebraMap ℚ_[p] L).injective
        simpa [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] L] using hab
      exact Subtype.coe_injective hq
    have h' : algebraMap ℤ_[p] L c * x = 0 := by
      simpa [Algebra.smul_def] using h
    rcases mul_eq_zero.mp h' with hc | hx
    · left; exact hinj (by simpa using hc)
    · right; exact hx

/-- The integers of L are torsion-free over Z_p. -/
instance noZeroSMulDivisors_integers : NoZeroSMulDivisors ℤ_[p] (Integers L) where
  eq_zero_or_eq_zero_of_smul_eq_zero {c x} h := by
    have h' : algebraMap ℤ_[p] (Integers L) c * x = 0 := by
      simpa [Algebra.smul_def] using h
    rcases mul_eq_zero.mp h' with hc | hx
    · left
      apply Subtype.coe_injective
      have hc' : algebraMap ℤ_[p] L c = 0 := by
        simpa [IsScalarTower.algebraMap_apply ℤ_[p] (Integers L) L] using congrArg Subtype.val hc
      exact (algebraMap ℚ_[p] L).injective (by simpa using hc')
    · right; exact hx

#print axioms maximalIdeal_isPrime
#print axioms noZeroSMulDivisors_integers
end LeanFormal.IUT.XiFPaper.Mzk1G1LocalFieldInstancesActual
