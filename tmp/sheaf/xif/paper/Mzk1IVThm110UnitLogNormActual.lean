import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.Normed.Module.Basic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitLogNormActual
open LeanFormal.IUT.LocalFieldIntegralUnits
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
variable {p : Nat} [Fact p.Prime]
variable [NormedAlgebra ℚ_[p] K] [NormOneClass K]
/-- Coprime p n implies p-adic valuation zero. -/
theorem padicValNat_eq_zero_of_coprime {n : Nat}
    (h : Nat.Coprime p n) : padicValNat p n = 0 := by
  exact padicValNat.eq_zero_of_not_dvd
    ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp h)
/-- Coprime p n implies the natural number n is a norm-one element of K. -/
theorem norm_natCast_eq_one_of_coprime {n : Nat}
    (h : Nat.Coprime p n) : ‖(n : K)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[p] K) n]
  rw [norm_algebraMap' (𝕜 := ℚ_[p]) (𝕜' := K)]
  exact (Padic.norm_natCast_eq_one_iff (p := p)).mpr h
#check padicValNat_eq_zero_of_coprime
#check norm_natCast_eq_one_of_coprime
end LeanFormal.IUT.XiFPaper.Mzk1IVThm110UnitLogNormActual
end