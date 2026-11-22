/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import LeanFormal.IUT.IUTIV.Estimates.DifferentDegreeUpperBound
import Mathlib.Tactic
/-! # p=2 norm/addVal bridge: uniformizer pi, N*eK comparison -/
noncomputable section
namespace LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.IUTIV.Estimates
open scoped NNReal NormedField
variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : Nat} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra (Padic p) K]
variable [FiniteDimensional (Padic p) K]
variable [hDVR : IsDiscreteValuationRing (Integers K)]
include localNormedAlgebra
/-- For an actual uniformizer `pi`, the norm comparison is the `addVal` threshold. -/
theorem norm_le_norm_natCast_iff_addVal_ge
    (π : Integers K) (hπ : Irreducible π)
    (x : Integers K) (hx : x ≠ 0) (N : Nat) :
    ‖(x : K)‖ ≤ ‖((((p : Nat) ^ N : Nat)) : K)‖ ↔
      N * logShellRamificationExponent (K := K) (p := p) ≤
        (IsDiscreteValuationRing.addVal (Integers K) x).toNat := by
  classical
  let e := logShellRamificationExponent (K := K) (p := p)
  have hepos : 0 < e := logShellRamificationExponent_pos (K := K) (p := p)
  have hp0 : ((p : Nat) : Integers K) ≠ 0 := prime_ne_zero_integers (K := K) (p := p)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hπ
  have hn : n = e := by
    have hval := congrArg (fun z : Integers K => IsDiscreteValuationRing.addVal (Integers K) z) hu
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_of_unit,
      zero_add, hπ.addVal_pow] at hval
    have hpval : IsDiscreteValuationRing.addVal (Integers K) ((p : Nat) : Integers K) = (e : ℕ∞) := by
      simpa [e, ramifiedPrimeAddVal] using addVal_prime_eq_ramificationExponent (K := K) (p := p)
    rw [hpval] at hval
    exact (Nat.cast_injective hval).symm
  have hn1 : ‖((p : Nat) : K)‖ = (p : ℝ)⁻¹ := by
    calc ‖((p : Nat) : K)‖ = ‖((p : Nat) : ℚ_[p])‖ := by
          simpa only [map_natCast] using norm_algebraMap' K ((p : Nat) : ℚ_[p])
      _ = (p : ℝ)⁻¹ := Padic.norm_p
  have hcoep : ((p : Nat) : K) = ((u : Integers K) : K) * (π : K) ^ n := by
    have h := congrArg (fun z : Integers K => (z : K)) hu
    simpa [Subring.coe_mul, Subring.coe_pow] using h
  have hpnorm : ‖((p : Nat) : K)‖ = ‖(π : K)‖ ^ n := by
    calc ‖((p : Nat) : K)‖ = ‖((u : Integers K) : K) * (π : K) ^ n‖ :=
            congrArg (fun z : K => ‖z‖) hcoep
      _ = ‖((u : Integers K) : K)‖ * ‖(π : K) ^ n‖ := norm_mul _ _
      _ = 1 * ‖(π : K) ^ n‖ := by rw [norm_unit_eq_one (K := K) u]
      _ = ‖(π : K)‖ ^ n := by rw [one_mul, norm_pow]
  have hcoenorm : ‖(π : K) ^ n‖ = ‖((p : Nat) : K)‖ := by
    rw [norm_pow]
    exact hpnorm.symm
  have hnorm_e : ‖(π : K)‖ ^ e = (p : ℝ)⁻¹ := by
    rw [← hn, ← norm_pow, hcoenorm, hn1]
  have hπpos : 0 < ‖(π : K)‖ := by
    apply norm_pos_iff.mpr
    intro hzero
    apply hπ.ne_zero
    exact Subtype.coe_injective (by simpa using hzero)
  have hπlt : ‖(π : K)‖ < 1 := by
    by_contra hge
    have hge1 : 1 ≤ ‖(π : K)‖ := le_of_not_gt hge
    have hpowge : 1 ≤ ‖(π : K)‖ ^ e := one_le_pow₀ hge1
    rw [hnorm_e] at hpowge
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hinvlt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    linarith
  letI : IsDiscreteValuationRing (Integers K) :=
    integersIsDiscreteValuationRing (p := p) (L := K)
  have hnorm_pow : ‖((((p : Nat) ^ N : Nat)) : K)‖ = ‖(π : K)‖ ^ (e * N) := by
    have hnormpN : ‖((((p : Nat) ^ N : Nat)) : K)‖ = (p : ℝ) ^ (-(N : ℤ)) := by
      rw [norm_natCast_eq_prime_zpow_neg_padicValNat (K := K) (p := p) (p ^ N)]
      · rw [padicValNat.prime_pow]
      · exact pow_pos (Fact.out : p.Prime).pos N
    rw [hnormpN, zpow_neg, zpow_natCast, ← inv_pow, ← hnorm_e, ← pow_mul]
  obtain ⟨m, v, hxeq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  have hcoex : (x : K) = ((v : Integers K) : K) * (π : K) ^ m := by
    have h := congrArg (fun z : Integers K => (z : K)) hxeq
    simpa [Subring.coe_mul, Subring.coe_pow] using h
  have hadd : IsDiscreteValuationRing.addVal (Integers K) x = (m : ℕ∞) := by
    rw [hxeq, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add, hπ.addVal_pow]
  have hnormx : ‖(x : K)‖ = ‖(π : K)‖ ^ m := by
    simpa [hcoex, norm_mul, norm_unit_eq_one (K := K) v, norm_pow]
  rw [hnormx, hnorm_pow, hadd, ENat.toNat_coe]
  rw [pow_le_pow_iff_right_of_lt_one₀ hπpos hπlt]
  rw [Nat.mul_comm e N]
end LeanFormal.IUT.LocalFieldLogarithm
end