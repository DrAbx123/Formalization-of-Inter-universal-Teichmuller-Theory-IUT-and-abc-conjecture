import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmGalois
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Actual Galois-fixed integral units descend to the base field

The source of a pre-log-shell is the image of fixed original units,
not the entire fixed field of a rationalized group. The fixed-unit
subgroup here is proved to be the image of the actual base integer
units. The upper field need not be complete or proper, so this descent
also applies before completion of an algebraic closure.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {K L : Type*} [NormedField K] [NormedField L] [NormedAlgebra K L]

theorem isometry_localField_algebraMap : Isometry (algebraMap K L) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, norm_algebraMap']

variable [IsUltrametricDist K] [IsUltrametricDist L]
variable {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] K] [NormedAlgebra ℚ_[p] L]
variable [IsScalarTower ℚ_[p] K L] [Algebra.IsAlgebraic ℚ_[p] L] [IsGalois K L]

/-- Raw fixed units, before taking their logarithmic image. -/
def localGaloisFixedIntegralUnits : Subgroup (Integers L)ˣ where
  carrier := {u | ∀ σ : L ≃ₐ[K] L, localGaloisUnitMap (σ.restrictScalars ℚ_[p]) u = u}
  one_mem' := by intro σ; exact map_one _
  mul_mem' := by
    intro u v hu hv σ
    rw [map_mul, hu σ, hv σ]
  inv_mem' := by
    intro u hu σ
    rw [map_inv, hu σ]

theorem mem_localGaloisFixedIntegralUnits_iff (u : (Integers L)ˣ) :
    u ∈ localGaloisFixedIntegralUnits (K := K) (p := p) ↔
      ∃ v : (Integers K)ˣ,
        integralUnitMap (algebraMap K L)
          (isometry_localField_algebraMap (K := K) (L := L)) v = u := by
  constructor
  · intro hu
    have hfixed : ∀ σ : L ≃ₐ[K] L, σ (u.val : L) = (u.val : L) := by
      intro σ
      exact congrArg (fun v : (Integers L)ˣ => (v.val : L)) (hu σ)
    obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (u.val : L)).mpr hfixed
    have hnorm : ‖a‖ = 1 := by
      rw [← norm_algebraMap' L a, ha]
      exact norm_unit_eq_one u
    refine ⟨unitOfNormOne ⟨a, hnorm⟩, ?_⟩
    apply Units.ext
    apply Subtype.ext
    exact ha
  · rintro ⟨v, rfl⟩ σ
    apply Units.ext
    apply Subtype.ext
    exact σ.commutes (v.val : K)

/-- The actual base-unit map lands in the actual fixed subgroup. -/
def baseUnitsToGaloisFixed : (Integers K)ˣ →*
    localGaloisFixedIntegralUnits (K := K) (L := L) (p := p) :=
  (integralUnitMap (algebraMap K L) (isometry_localField_algebraMap (K := K) (L := L))).codRestrict
    _ (fun v => (mem_localGaloisFixedIntegralUnits_iff (p := p) _).mpr ⟨v, rfl⟩)

def baseUnitsGaloisFixedEquiv : (Integers K)ˣ ≃*
    localGaloisFixedIntegralUnits (K := K) (L := L) (p := p) := by
  apply MulEquiv.ofBijective (baseUnitsToGaloisFixed (K := K) (L := L) (p := p))
  constructor
  · intro u v h
    apply Units.ext
    apply Subtype.ext
    apply (algebraMap K L).injective
    exact congrArg
      (fun w : localGaloisFixedIntegralUnits (K := K) (L := L) (p := p) => (w.val.val : L)) h
  · intro u
    obtain ⟨v, hv⟩ := (mem_localGaloisFixedIntegralUnits_iff (p := p) u.val).mp u.property
    exact ⟨v, Subtype.ext hv⟩

theorem baseUnitsGaloisFixedEquiv_val (u : (Integers K)ˣ) :
    (baseUnitsGaloisFixedEquiv (K := K) (L := L) (p := p) u).val =
      integralUnitMap (algebraMap K L) (isometry_localField_algebraMap (K := K) (L := L)) u := rfl

end

end LeanFormal.IUT.LocalFieldLogarithm
