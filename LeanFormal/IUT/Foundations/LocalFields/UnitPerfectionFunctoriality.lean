import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitPerfectionTopology
import LeanFormal.IUT.Foundations.LocalFields.AlgebraicUnitLogarithmRationalization

/-!
# Canonical maps of actual unit perfections

Localize the map of original integral units, without using logarithms
to define the source map. The resulting rational linear map commutes
with logarithms from finite local fields into algebraic extensions.
-/

namespace LeanFormal.IUT.LocalFieldLogarithm

open LeanFormal.IUT.LocalFieldIntegralUnits

noncomputable section

variable {F L : Type*} [NormedField F] [NormedField L]
variable [IsUltrametricDist F] [IsUltrametricDist L]

def integralUnitMapIntLinear (e : F →+* L) (he : Isometry e) :
    Additive (Integers F)ˣ →ₗ[ℤ] Additive (Integers L)ˣ :=
  AddMonoidHom.toIntLinearMap {
    toFun := fun u => Additive.ofMul (integralUnitMap e he u.toMul)
    map_zero' := by
      change integralUnitMap e he 1 = 1
      exact map_one _
    map_add' := by
      intro u v
      change integralUnitMap e he (u.toMul * v.toMul) = _
      exact map_mul _ _ _ }

def unitPerfectionMap (e : F →+* L) (he : Isometry e) :
    UnitLogPerfection F →ₗ[ℚ] UnitLogPerfection L := by
  letI : Module ℤ (UnitLogPerfection F) :=
    OreLocalization.instModuleOfIsScalarTower (R := ℤ) (R₀ := ℤ)
      (S := nonZeroDivisors ℤ) (X := Additive (Integers F)ˣ)
  letI : Module ℤ (UnitLogPerfection L) :=
    OreLocalization.instModuleOfIsScalarTower (R := ℤ) (R₀ := ℤ)
      (S := nonZeroDivisors ℤ) (X := Additive (Integers L)ˣ)
  let g := IsLocalizedModule.map (nonZeroDivisors ℤ)
    (LocalizedModule.mkLinearMap (nonZeroDivisors ℤ) (Additive (Integers F)ˣ))
    (LocalizedModule.mkLinearMap (nonZeroDivisors ℤ) (Additive (Integers L)ˣ))
    (integralUnitMapIntLinear e he)
  exact { g.toAddMonoidHom with map_smul' := fun q x => map_rat_smul g.toAddMonoidHom q x }

theorem unitPerfectionMap_mk (e : F →+* L) (he : Isometry e)
    (u : (Integers F)ˣ) (a : nonZeroDivisors ℤ) :
    unitPerfectionMap e he (LocalizedModule.mk (Additive.ofMul u) a) =
      LocalizedModule.mk (Additive.ofMul (integralUnitMap e he u)) a := by
  letI : Module ℤ (UnitLogPerfection F) :=
    OreLocalization.instModuleOfIsScalarTower (R := ℤ) (R₀ := ℤ)
      (S := nonZeroDivisors ℤ) (X := Additive (Integers F)ˣ)
  letI : Module ℤ (UnitLogPerfection L) :=
    OreLocalization.instModuleOfIsScalarTower (R := ℤ) (R₀ := ℤ)
      (S := nonZeroDivisors ℤ) (X := Additive (Integers L)ˣ)
  exact IsLocalizedModule.map_LocalizedModules (nonZeroDivisors ℤ)
    (integralUnitMapIntLinear e he) (Additive.ofMul u) a

variable [CharZero L] {p : ℕ} [Fact p.Prime] [NormedAlgebra ℚ_[p] L]
variable [Algebra.IsAlgebraic ℚ_[p] L]

theorem algebraicUnitPerfectionEquiv_mk (u : (Integers L)ˣ) (a : nonZeroDivisors ℤ) :
    algebraicUnitPerfectionEquiv (p := p) (LocalizedModule.mk (Additive.ofMul u) a) =
      ((a : ℤ) : L)⁻¹ * algebraicUnitLog (p := p) u := by
  have ha : ((a : ℤ) : L) ≠ 0 :=
    Int.cast_ne_zero.mpr (mem_nonZeroDivisors_iff_ne_zero.mp a.property)
  have hcancel : (a : ℤ) • (LocalizedModule.mk (Additive.ofMul u) a : UnitLogPerfection L) =
      LocalizedModule.mk (Additive.ofMul u) 1 := by
    letI : Module ℤ (UnitLogPerfection L) :=
      OreLocalization.instModuleOfIsScalarTower (R := ℤ) (R₀ := ℤ)
        (S := nonZeroDivisors ℤ) (X := Additive (Integers L)ˣ)
    rw [← Int.cast_smul_eq_zsmul ℤ, LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_cancel a _
  have hvalue := congrArg (algebraicUnitPerfectionEquiv (p := p)) hcancel
  rw [map_zsmul, algebraicUnitPerfectionEquiv_mk_one, zsmul_eq_mul] at hvalue
  rw [← hvalue, inv_mul_cancel_left₀ ha]

variable [CharZero F] [CompleteSpace F] [ProperSpace F] [NormedAlgebra ℚ_[p] F]

theorem unitPerfectionMap_log_commute (e : F →+* L) (he : Isometry e)
    (x : UnitLogPerfection F) :
    algebraicUnitPerfectionEquiv (p := p) (unitPerfectionMap e he x) =
      e (unitLogPerfectionEquiv (p := p) x) := by
  induction x using LocalizedModule.induction_on with
  | _ u a =>
    change algebraicUnitPerfectionEquiv (p := p)
      (unitPerfectionMap e he (LocalizedModule.mk (Additive.ofMul u.toMul) a)) =
      e (unitLogPerfectionEquiv (p := p) (LocalizedModule.mk (Additive.ofMul u.toMul) a))
    rw [unitPerfectionMap_mk, algebraicUnitPerfectionEquiv_mk,
      unitLogPerfectionEquiv_mk (p := p) u.toMul a,
      algebraicUnitLog_eq_map (p := p), map_mul, map_inv₀, map_intCast]

end

end LeanFormal.IUT.LocalFieldLogarithm
