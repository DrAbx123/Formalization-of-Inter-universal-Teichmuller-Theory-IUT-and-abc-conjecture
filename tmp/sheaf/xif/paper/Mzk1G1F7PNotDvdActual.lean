/-
Route 8.5 F7 tame Kummer valuation: the p ∤ n input layer.

For a finite extension L / Q_p, the rational integer n is a unit of the integer ring
O_L = Integers L as soon as p ∤ n. Consequently, for a uniformizer x (that is, addVal x = 1),
the derivative n * x ^ (n - 1) of x ^ n has additive DVR order exactly n - 1, the tame
different exponent.

Both proofs are unconditional and use only Mathlib plus the accepted Foundations/LocalFields
layer:

* p ∤ n makes n a norm-one element of L: the Q_p-algebra map of any normed algebra is norm
  preserving (norm_algebraMap', only NormOneClass is used), and norm-one elements of the
  valuation ring are units (LeanFormal.IUT.LocalFieldIntegralUnits.unitOfNormOne). No residue
  field and no extra hypothesis is introduced. The full finite-extension hypothesis set is
  nevertheless kept on the statement, because that is the consumer-facing interface.
* the additive order of the derivative is addVal_mul + addVal_pow + addVal_eq_zero_iff.

The IsDiscreteValuationRing (Integers L) instance is passed explicitly
(@IsDiscreteValuationRing.addVal ... (integersIsDiscreteValuationRing ...)), matching the
convention of IntegralLogShellRamificationInertia.ramifiedPrimeAddVal: that instance is not a
global instance, so statements must fix it explicitly to stay independent of typeclass search.
-/
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Tactic

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1G1F7PNotDvdActual

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion

variable {p : Nat} [Fact p.Prime] {L : Type*} [NormedField L] [CharZero L] [CompleteSpace L]
  [IsUltrametricDist L] [ProperSpace L] [NormedAlgebra ℚ_[p] L] [FiniteDimensional ℚ_[p] L]

/-- A rational integer n with p ∤ n is a unit of the integer ring of a finite extension of
Q_p. The proof goes through the norm: n has norm one in L, and norm-one elements of the
valuation ring are units. -/
theorem natCast_isUnit_of_not_dvd (n : Nat) (h : ¬ p ∣ n) : IsUnit (n : Integers L) := by
  have hcop : p.Coprime n := (Fact.out : p.Prime).coprime_iff_not_dvd.mpr h
  have hnormQp : ‖(n : ℚ_[p])‖ = 1 := Padic.norm_natCast_eq_one_iff.mpr hcop
  have hnormL : ‖(n : L)‖ = 1 := by
    have heq : ‖(n : L)‖ = ‖(n : ℚ_[p])‖ := by
      simpa only [map_natCast] using norm_algebraMap' L (n : ℚ_[p])
    rw [heq, hnormQp]
  let u : (Integers L)ˣ := unitOfNormOne ⟨(n : L), hnormL⟩
  have hval : (u : Integers L) = (n : Integers L) := Subtype.ext rfl
  rw [← hval]
  exact u.isUnit

/-- The additive DVR order of n in the integer ring vanishes when p ∤ n. -/
theorem addVal_natCast_eq_zero_of_not_dvd (n : Nat) (h : ¬ p ∣ n) :
    @IsDiscreteValuationRing.addVal (Integers L) _ _
      (integersIsDiscreteValuationRing (p := p) (L := L)) (n : Integers L) = 0 := by
  haveI : IsDiscreteValuationRing (Integers L) :=
    integersIsDiscreteValuationRing (p := p) (L := L)
  exact IsDiscreteValuationRing.addVal_eq_zero_iff.mpr (natCast_isUnit_of_not_dvd n h)

/-- Tame different exponent: if x is a uniformizer of Integers L (its additive order is one)
and p ∤ n, then the derivative n * x ^ (n - 1) of x ^ n has additive order exactly n - 1. -/
theorem addVal_natCast_mul_pow_sub_one_of_not_dvd (n : Nat) (x : Integers L)
    (h : ¬ p ∣ n)
    (hx : @IsDiscreteValuationRing.addVal (Integers L) _ _
      (integersIsDiscreteValuationRing (p := p) (L := L)) x = 1) :
    @IsDiscreteValuationRing.addVal (Integers L) _ _
      (integersIsDiscreteValuationRing (p := p) (L := L))
      ((n : Integers L) * x ^ (n - 1)) = (n - 1 : Nat) := by
  haveI : IsDiscreteValuationRing (Integers L) :=
    integersIsDiscreteValuationRing (p := p) (L := L)
  rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, hx,
    addVal_natCast_eq_zero_of_not_dvd n h, zero_add]
  simp

#check @natCast_isUnit_of_not_dvd
#check @addVal_natCast_eq_zero_of_not_dvd
#check @addVal_natCast_mul_pow_sub_one_of_not_dvd
#print axioms natCast_isUnit_of_not_dvd
#print axioms addVal_natCast_eq_zero_of_not_dvd
#print axioms addVal_natCast_mul_pow_sub_one_of_not_dvd

end LeanFormal.IUT.XiFPaper.Mzk1G1F7PNotDvdActual
