import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmKernel
import LeanFormal.IUT.Foundations.LocalFields.LogarithmLocalInverse
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldIntegralTensorSpan
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The actual rationalized unit group and the local logarithmic field

Invert the nonzero integers in the additive form of the actual integral
unit group. Its logarithm identifies the resulting localized module with
the local field: all denominators act invertibly, every field element
has an integer multiple in the actual logarithmic image, and equality
of logarithms is killed by an integer because the kernel is torsion.
No perfection or field-identification obligation is postulated.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]
variable {p : ℕ} [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]

include localNormedAlgebra

def unitLogAddHom : Additive (Integers K)ˣ →+ K where
  toFun u := unitLog u.toMul
  map_zero' := unitLog_one (p := p)
  map_add' u v := unitLog_mul (p := p) u.toMul v.toMul

def unitLogIntLinear : Additive (Integers K)ˣ →ₗ[ℤ] K :=
  (unitLogAddHom (p := p)).toIntLinearMap

/-- Denominators are actually cleared into the unit logarithmic image. -/
theorem exists_integer_smul_eq_unitLog (x : K) :
    ∃ a : nonZeroDivisors ℤ, ∃ u : (Integers K)ˣ, (a : ℤ) • x = unitLog u := by
  let d := logShellScale p
  have hd : d ≠ 0 := ne_of_gt (logShellScale_pos (p := p))
  have hdK : ‖(d : K)‖ < 1 :=
    (norm_logShellScale_lt_half (K := K) (p := p)).trans (by norm_num)
  obtain ⟨n, hn⟩ :=
    LocalFieldIntegralTensorSpan.exists_integer_pow_mul_mem_unitBall d hdK x
  let y : Integers K := ⟨(d : K) ^ n * x, (mem_integers_iff _).mpr hn⟩
  obtain ⟨u, _, hu⟩ := exists_unitLog_eq_scale_mul (p := p) y
  let a : nonZeroDivisors ℤ := ⟨(d : ℤ) ^ (n + 1),
    mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero _ (Nat.cast_ne_zero.mpr hd))⟩
  refine ⟨a, u, ?_⟩
  rw [hu]
  change ((d : ℤ) ^ (n + 1)) • x = (d : K) * ((d : K) ^ n * x)
  simp only [zsmul_eq_mul, Int.cast_pow, Int.cast_natCast]
  ring

theorem unitLog_isLocalizedModule :
    IsLocalizedModule (nonZeroDivisors ℤ) (unitLogIntLinear (K := K) (p := p)) where
  map_units a := by
    letI := isLocalizedModule_id (S := nonZeroDivisors ℤ) (M := K) (R' := ℚ)
    exact IsLocalizedModule.map_units (LinearMap.id : K →ₗ[ℤ] K) a
  surj x := by
    obtain ⟨a, u, hu⟩ := exists_integer_smul_eq_unitLog (p := p) x
    exact ⟨(Additive.ofMul u, a), hu⟩
  exists_of_eq {u v} huv := by
    have hlog : unitLog u.toMul = unitLog v.toMul := huv
    have hzero : unitLog (u.toMul * v.toMul⁻¹) = 0 := by
      rw [unitLog_mul (p := p), unitLog_inv (p := p), hlog, add_neg_cancel]
    obtain ⟨n, hn, hpow⟩ := (unitLog_eq_zero_iff_exists_pow_eq_one (p := p) _).mp hzero
    rw [mul_pow, inv_pow, mul_inv_eq_one] at hpow
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr
      (Nat.cast_ne_zero.mpr (ne_of_gt hn))⟩, ?_⟩
    change u.toMul ^ (n : ℤ) = v.toMul ^ (n : ℤ)
    simpa only [zpow_natCast] using hpow

/-- The concrete perfection: localization of the actual unit group. -/
abbrev UnitLogPerfection (K : Type*) [NormedField K] [IsUltrametricDist K] :=
  LocalizedModule (nonZeroDivisors ℤ) (Additive (Integers K)ˣ)

instance unitLogPerfectionRatModule : Module ℚ (UnitLogPerfection K) :=
  LocalizedModule.moduleOfIsLocalization
    (S := nonZeroDivisors ℤ) (M := Additive (Integers K)ˣ) (T := ℚ)

/-- The rationalized source is the field by the actual logarithm. -/
def unitLogPerfectionEquiv : UnitLogPerfection K ≃ₗ[ℚ] K := by
  letI : Module ℤ (UnitLogPerfection K) :=
    OreLocalization.instModuleOfIsScalarTower (R := ℤ) (R₀ := ℤ)
      (S := nonZeroDivisors ℤ) (X := Additive (Integers K)ˣ)
  letI := unitLog_isLocalizedModule (K := K) (p := p)
  let e := IsLocalizedModule.iso (nonZeroDivisors ℤ) (unitLogIntLinear (K := K) (p := p))
  exact { e.toAddEquiv with map_smul' := fun q x => map_rat_smul e.toAddEquiv q x }

theorem unitLogPerfectionEquiv_mk_one (u : (Integers K)ˣ) :
    unitLogPerfectionEquiv (p := p) (LocalizedModule.mk (Additive.ofMul u) 1) = unitLog u := by
  letI : Module ℤ (UnitLogPerfection K) :=
    OreLocalization.instModuleOfIsScalarTower (R := ℤ) (R₀ := ℤ)
      (S := nonZeroDivisors ℤ) (X := Additive (Integers K)ˣ)
  letI := unitLog_isLocalizedModule (K := K) (p := p)
  change (IsLocalizedModule.iso (nonZeroDivisors ℤ) (unitLogIntLinear (K := K) (p := p)))
    (LocalizedModule.mk (Additive.ofMul u) 1) = unitLog u
  exact IsLocalizedModule.iso_mk_one _ _ _

end

end LeanFormal.IUT.LocalFieldLogarithm
