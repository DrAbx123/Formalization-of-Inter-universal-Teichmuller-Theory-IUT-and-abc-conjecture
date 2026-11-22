/- Route 8.5 F7 tame Kummer valuation core: in a discrete valuation ring, the derivative
n * x^(n-1) of x^n has additive order (n-1) * ord(x) + ord(n); if x is a uniformizer and n is a
unit (p not dividing n), this is exactly n-1, the tame different exponent. -/
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentUpperBound
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1KummerTameValuationActual

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.LocalDifferentUpperBound

/-- In a DVR, the additive order of n * x^(n-1) is (n-1)*ord(x) + ord(n). -/
theorem addVal_natCast_mul_pow_sub_one {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (x : R) (n : Nat) :
    IsDiscreteValuationRing.addVal R ((n : R) * x ^ (n - 1)) =
      IsDiscreteValuationRing.addVal R (n : R) + (n - 1) • IsDiscreteValuationRing.addVal R x := by
  rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow]

/-- Tame Kummer valuation core: if x is a uniformizer (addVal x = 1) and n is a unit, then
n * x^(n-1) has additive order n - 1. -/
theorem addVal_natCast_mul_pow_sub_one_of_unit {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (x : R) (n : Nat)
    (hx : IsDiscreteValuationRing.addVal R x = 1)
    (hn : IsUnit (n : R)) :
    IsDiscreteValuationRing.addVal R ((n : R) * x ^ (n - 1)) = (n - 1 : Nat) := by
  rw [addVal_natCast_mul_pow_sub_one, hx]
  have hn0 : IsDiscreteValuationRing.addVal R (n : R) = 0 :=
    (IsDiscreteValuationRing.addVal_eq_zero_iff).mpr hn
  rw [hn0, zero_add]
  simp

/-- The p-adic version: for the integer ring of a finite extension of Q_p, the derivative
n * x^(n-1) of a uniformizer x has DVR order n-1 when n is a unit. -/
theorem addVal_derivative_eq_ramification_sub_one {p : Nat} [Fact p.Prime]
    {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L] [IsUltrametricDist L]
    [ProperSpace L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]
    [IsDiscreteValuationRing (Integers L)]
    (x : Integers L) (n : Nat)
    (hx : IsDiscreteValuationRing.addVal (Integers L) x = 1)
    (hn : IsUnit (n : Integers L)) :
    IsDiscreteValuationRing.addVal (Integers L) ((n : Integers L) * x ^ (n - 1)) =
      (n - 1 : Nat) :=
  addVal_natCast_mul_pow_sub_one_of_unit x n hx hn

#print axioms addVal_natCast_mul_pow_sub_one
#print axioms addVal_natCast_mul_pow_sub_one_of_unit
#print axioms addVal_derivative_eq_ramification_sub_one
end LeanFormal.IUT.XiFPaper.Mzk1G1KummerTameValuationActual
