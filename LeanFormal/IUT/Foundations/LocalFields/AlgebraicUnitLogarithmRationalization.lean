import LeanFormal.IUT.Foundations.LocalFields.AlgebraicUnitLogarithmHom
import LeanFormal.IUT.Foundations.LocalFields.AlgebraicElementFiniteCarrier

/-!
# Actual unit perfection in a possibly noncomplete algebraic Qp extension

The logarithm makes the ambient field the localization of its actual
integer units at the nonzero integers. Denominators are cleared in the
finite complete carrier of each field element. Equality is killed by an
integer because the actual logarithm kernel consists precisely of torsion.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {Ω : Type*} [NormedField Ω] [CharZero Ω] [IsUltrametricDist Ω]
variable {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] Ω]
variable [Algebra.IsAlgebraic ℚ_[p] Ω]

def algebraicUnitLogAddHom : Additive (Integers Ω)ˣ →+ Ω where
  toFun u := algebraicUnitLog (p := p) u.toMul
  map_zero' := algebraicUnitLog_one (p := p)
  map_add' u v := algebraicUnitLog_mul (p := p) u.toMul v.toMul

def algebraicUnitLogIntLinear : Additive (Integers Ω)ˣ →ₗ[ℤ] Ω :=
  (algebraicUnitLogAddHom (p := p)).toIntLinearMap

theorem exists_integer_smul_eq_algebraicUnitLog (x : Ω) :
    ∃ a : nonZeroDivisors ℤ, ∃ u : (Integers Ω)ˣ,
      (a : ℤ) • x = algebraicUnitLog (p := p) u := by
  let F := finiteElementField (p := p) x
  let he := isometry_intermediateField_inclusion F
  obtain ⟨a, u, hu⟩ := exists_integer_smul_eq_unitLog (p := p) (finiteElementLift (p := p) x)
  refine ⟨a, integralUnitMap F.val.toRingHom he u, ?_⟩
  rw [algebraicUnitLog_eq_map (p := p), ← hu, map_zsmul]
  rfl

theorem algebraicUnitLog_isLocalizedModule :
    IsLocalizedModule (nonZeroDivisors ℤ) (algebraicUnitLogIntLinear (Ω := Ω) (p := p)) where
  map_units a := by
    letI := isLocalizedModule_id (S := nonZeroDivisors ℤ) (M := Ω) (R' := ℚ)
    exact IsLocalizedModule.map_units (LinearMap.id : Ω →ₗ[ℤ] Ω) a
  surj x := by
    obtain ⟨a, u, hu⟩ := exists_integer_smul_eq_algebraicUnitLog (p := p) x
    exact ⟨(Additive.ofMul u, a), hu⟩
  exists_of_eq {u v} huv := by
    have hlog : algebraicUnitLog (p := p) u.toMul = algebraicUnitLog (p := p) v.toMul := huv
    have hzero : algebraicUnitLog (p := p) (u.toMul * v.toMul⁻¹) = 0 := by
      rw [algebraicUnitLog_mul, algebraicUnitLog_inv, hlog, add_neg_cancel]
    obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp
      ((algebraicUnitLog_eq_zero_iff_isOfFinOrder (p := p) _).mp hzero)
    rw [mul_pow, inv_pow, mul_inv_eq_one] at hpow
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr
      (Nat.cast_ne_zero.mpr (ne_of_gt hn))⟩, ?_⟩
    change u.toMul ^ (n : ℤ) = v.toMul ^ (n : ℤ)
    simpa only [zpow_natCast] using hpow

def algebraicUnitPerfectionEquiv : UnitLogPerfection Ω ≃ₗ[ℚ] Ω := by
  letI : Module ℤ (UnitLogPerfection Ω) :=
    OreLocalization.instModuleOfIsScalarTower (R := ℤ) (R₀ := ℤ)
      (S := nonZeroDivisors ℤ) (X := Additive (Integers Ω)ˣ)
  letI := algebraicUnitLog_isLocalizedModule (Ω := Ω) (p := p)
  let e := IsLocalizedModule.iso (nonZeroDivisors ℤ)
    (algebraicUnitLogIntLinear (Ω := Ω) (p := p))
  exact { e.toAddEquiv with map_smul' := fun q x => map_rat_smul e.toAddEquiv q x }

theorem algebraicUnitPerfectionEquiv_mk_one (u : (Integers Ω)ˣ) :
    algebraicUnitPerfectionEquiv (p := p) (LocalizedModule.mk (Additive.ofMul u) 1) =
      algebraicUnitLog (p := p) u := by
  letI : Module ℤ (UnitLogPerfection Ω) :=
    OreLocalization.instModuleOfIsScalarTower (R := ℤ) (R₀ := ℤ)
      (S := nonZeroDivisors ℤ) (X := Additive (Integers Ω)ˣ)
  letI := algebraicUnitLog_isLocalizedModule (Ω := Ω) (p := p)
  exact IsLocalizedModule.iso_mk_one _ _ _

/-- The action is explicit, so it does not compete with the finite-field
action instance when the ambient algebraic extension happens to be finite. -/
abbrev algebraicUnitPerfectionGaloisAction :
    MulAction (Ω ≃ₐ[ℚ_[p]] Ω) (UnitLogPerfection Ω) where
  smul σ x := (algebraicUnitPerfectionEquiv (p := p)).symm
    (σ (algebraicUnitPerfectionEquiv (p := p) x))
  one_smul x := (algebraicUnitPerfectionEquiv (p := p)).symm_apply_apply x
  mul_smul σ τ x := by
    change (algebraicUnitPerfectionEquiv (p := p)).symm
        ((σ * τ) (algebraicUnitPerfectionEquiv (p := p) x)) =
      (algebraicUnitPerfectionEquiv (p := p)).symm
        (σ (algebraicUnitPerfectionEquiv (p := p)
          ((algebraicUnitPerfectionEquiv (p := p)).symm
            (τ (algebraicUnitPerfectionEquiv (p := p) x)))))
    rw [LinearEquiv.apply_symm_apply]
    rfl

theorem algebraicUnitPerfectionEquiv_galois_smul
    (σ : Ω ≃ₐ[ℚ_[p]] Ω) (x : UnitLogPerfection Ω) :
    letI := algebraicUnitPerfectionGaloisAction (Ω := Ω) (p := p)
    algebraicUnitPerfectionEquiv (p := p) (σ • x) =
      σ (algebraicUnitPerfectionEquiv (p := p) x) :=
  (algebraicUnitPerfectionEquiv (p := p)).apply_symm_apply _

theorem algebraicUnitPerfection_mk_galois_smul
    (σ : Ω ≃ₐ[ℚ_[p]] Ω) (u : (Integers Ω)ˣ) :
    letI := algebraicUnitPerfectionGaloisAction (Ω := Ω) (p := p)
    σ • (LocalizedModule.mk (Additive.ofMul u) 1 : UnitLogPerfection Ω) =
      LocalizedModule.mk (Additive.ofMul (σ • u)) 1 := by
  letI := algebraicUnitPerfectionGaloisAction (Ω := Ω) (p := p)
  apply (algebraicUnitPerfectionEquiv (p := p)).injective
  rw [algebraicUnitPerfectionEquiv_galois_smul,
    algebraicUnitPerfectionEquiv_mk_one, algebraicUnitPerfectionEquiv_mk_one,
    algebraicUnitLog_localGalois_smul]

end

end LeanFormal.IUT.LocalFieldLogarithm
