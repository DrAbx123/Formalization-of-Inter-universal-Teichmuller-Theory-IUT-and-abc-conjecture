/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.n8.closure.EtaUniformizerRelationActual
import tmp.sheaf.xif.paper.Node09H1aValuationActual
import Mathlib.Tactic

/-! # Actual F-place DVR uniformizer data -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09H1bDVRUniformizerActual
set_option maxHeartbeats 1000000
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open ABCBridge.N8.C3TensorTargetCorrection
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.XiFPaper.Node09H1aValuationActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped NNReal ENNReal Pointwise

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (ABCBridge.N8.C3TensorTargetCorrection.nativePrime X)) := ABCBridge.N8.C3TensorTargetCorrection.nativePrimeFact X
abbrev Kf (X : N8NativeInput l) : Type := CommonPrimeCompletion (ABCBridge.N8.C3TensorTargetCorrection.nativeFPlaceAtPrime X)

noncomputable def fPlaceUniformizer : Integers (Kf X) := by
  letI : IsDiscreteValuationRing (Integers (Kf X)) :=
    integers_isDiscreteValuationRing (E := Kf X) (p := ABCBridge.N8.C3TensorTargetCorrection.nativePrime X)
  exact Classical.choose (IsDiscreteValuationRing.exists_prime (Integers (Kf X)))

theorem fPlaceUniformizer_irreducible : Irreducible (fPlaceUniformizer X) := by
  letI : IsDiscreteValuationRing (Integers (Kf X)) :=
    integers_isDiscreteValuationRing (E := Kf X) (p := ABCBridge.N8.C3TensorTargetCorrection.nativePrime X)
  exact (Classical.choose_spec (IsDiscreteValuationRing.exists_prime (Integers (Kf X)))).irreducible

noncomputable def fPlaceDVRUniformizerData : FPlaceDVRUniformizerData X := by
  classical
  letI : IsDiscreteValuationRing (Integers (Kf X)) :=
    integers_isDiscreteValuationRing (E := Kf X) (p := ABCBridge.N8.C3TensorTargetCorrection.nativePrime X)
  have hne : fPlacePInt X ≠ 0 := fPlacePInt_ne_zero X
  let hfac : ∃ n : ℕ, ∃ u : (Integers (Kf X))ˣ,
      fPlacePInt X = u * fPlaceUniformizer X ^ n :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (R := Integers (Kf X)) hne (fPlaceUniformizer_irreducible X)
  let n : ℕ := Classical.choose hfac
  let u : (Integers (Kf X))ˣ := Classical.choose (Classical.choose_spec hfac)
  have hu : fPlacePInt X = u * fPlaceUniformizer X ^ n :=
    Classical.choose_spec (Classical.choose_spec hfac)
  have hnormp : ‖(fPlacePInt X : Kf X)‖ = ((ABCBridge.N8.C3TensorTargetCorrection.nativePrime X : ℝ))⁻¹ := by
    simpa [fPlacePInt, fPlaceP] using fPlaceP_norm X
  have hnormu : ‖((u : Integers (Kf X)) : Kf X)‖ = 1 :=
    norm_unit_eq_one (K := Kf X) u
  have hn : n ≠ 0 := by
    intro hn0
    have hnorm : ‖(fPlacePInt X : Kf X)‖ = 1 := by
      rw [hu, hn0, pow_zero, mul_one]
      exact hnormu
    rw [hnormp] at hnorm
    have hp1 : (ABCBridge.N8.C3TensorTargetCorrection.nativePrime X : ℝ) = 1 := by
      have hp0 : (0 : ℝ) < (ABCBridge.N8.C3TensorTargetCorrection.nativePrime X : ℝ) := by positivity
      field_simp [hp0.ne'] at hnorm
      linarith
    exact (Fact.out : Nat.Prime (ABCBridge.N8.C3TensorTargetCorrection.nativePrime X)).ne_one (by exact_mod_cast hp1)
  refine
    { pi := fPlaceUniformizer X
      irreducible := fPlaceUniformizer_irreducible X
      exponent := n
      exponent_ne_zero := hn
      unit := u
      factor := hu
      unit_norm_one := ?_
      unit_fixes_integers := ?_ }
  · simpa [Units.map] using hnormu
  · ext x
    simp only [Set.mem_smul_set, Units.map_apply, Units.val_mk, Subring.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_integers_iff] at hy ⊢
      have hval : ((u : Integers (Kf X)) : Kf X) * y = ((u : Integers (Kf X)) : Kf X) * y := rfl
      rw [norm_mul, hnormu, one_mul]
      exact hy
    · intro hx
      refine ⟨((u⁻¹ : (Integers (Kf X))ˣ) : Integers (Kf X)) * x, ?_, ?_⟩
      · rw [mem_integers_iff] at hx ⊢
        rw [norm_mul]
        have huinv : ‖((u⁻¹ : (Integers (Kf X))ˣ) : Kf X)‖ = 1 :=
          norm_unit_eq_one (K := Kf X) (u⁻¹)
        rw [huinv, one_mul]
        exact hx
      · simp only [Subring.coe_mul, Subring.coe_subtype, Units.val_inv]
        rw [← mul_assoc, Units.mul_inv, one_mul]

theorem fPlaceDVRUniformizerDataExists : FPlaceDVRUniformizerDataExists X :=
  ⟨fPlaceDVRUniformizerData X⟩

end LeanFormal.IUT.XiFPaper.Node09H1bDVRUniformizerActual
