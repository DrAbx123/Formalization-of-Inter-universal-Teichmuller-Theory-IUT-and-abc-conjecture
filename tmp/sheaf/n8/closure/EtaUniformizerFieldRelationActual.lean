import tmp.sheaf.n8.closure.EtaFPlaceDVRUniformizerDataActual
import tmp.sheaf.n8.closure.EtaUniformizerHaarActualAtF

/-!
# EtaUniformizerFieldRelationActual

Convert the actual DVR factorization `p = u * π^n` in the completion integers
into the field-unit relation `π^n = pUnit * u⁻¹`, then apply the actual F-place
uniformizer theorem.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaUniformizerFieldRelationActual

open LeanFormal.IUT
open MeasureTheory
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual
open LeanFormal.IUT.N8Closure.EtaValuedRankLeOneActual
open LeanFormal.IUT.N8Closure.EtaPStepNormLink
open LeanFormal.IUT.N8Closure.EtaFPlaceDVRUniformizerDataActual
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.N8Closure.EtaUniformizerHaarActualAtF
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

noncomputable def chosenPiK : (Kf X)ˣ :=
  Units.mk0 ((fPlaceDVRUniformizerData X).pi : Kf X)
    (by
      intro h
      exact (Irreducible.ne_zero (fPlaceDVRUniformizerData X).irreducible)
        (Subtype.ext h))

noncomputable def pDVRUnitK : (Kf X)ˣ :=
  Units.mk0 ((fPlaceDVRUniformizerData X).unit : Integers (Kf X)) (by
    intro h
    exact Units.ne_zero (fPlaceDVRUniformizerData X).unit (Subtype.ext h))

theorem pDVRUnitK_norm : ‖(pDVRUnitK X : Kf X)‖ = 1 :=
  (fPlaceDVRUniformizerData X).unit_norm_one

theorem pDVRUnitK_smul_integers :
    pDVRUnitK X • (Integers (Kf X) : Set (Kf X)) = (Integers (Kf X) : Set (Kf X)) :=
  (fPlaceDVRUniformizerData X).unit_fixes_integers

theorem factor_int :
    fPlacePInt X = (fPlaceDVRUniformizerData X).unit *
      (fPlaceDVRUniformizerData X).pi ^ (fPlaceDVRUniformizerData X).exponent :=
  (fPlaceDVRUniformizerData X).factor

theorem pUnit_val : (pUnit (p := nativePrime X) (K := Kf X) : Kf X) = fPlaceP X :=
  rfl

theorem p_eq_unit_pi_pow :
    (pUnit (p := nativePrime X) (K := Kf X) : Kf X) =
      (pDVRUnitK X : Kf X) * (chosenPiK X : Kf X) ^
        (fPlaceDVRUniformizerData X).exponent := by
  rw [pUnit_val]
  have h := congrArg (fun z : Integers (Kf X) => (z : Kf X)) (factor_int X)
  simpa [fPlacePInt, pDVRUnitK, chosenPiK, Units.val_mul,
    Units.val_pow_eq_pow_val] using h

theorem pi_pow_eq_pUnit_unit_inv :
    (chosenPiK X : (Kf X)ˣ) ^ (fPlaceDVRUniformizerData X).exponent =
      pUnit (p := nativePrime X) (K := Kf X) * (pDVRUnitK X)⁻¹ := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val]
  have h := p_eq_unit_pi_pow X
  have hu : (pDVRUnitK X : Kf X) ≠ 0 := Units.ne_zero (pDVRUnitK X)
  field_simp [hu]
  rw [h]
  ring

theorem pDVRUnitK_inv_smul_integers :
    (pDVRUnitK X)⁻¹ • (Integers (Kf X) : Set (Kf X)) =
      (Integers (Kf X) : Set (Kf X)) := by
  calc
    (pDVRUnitK X)⁻¹ • (Integers (Kf X) : Set (Kf X)) =
        (pDVRUnitK X)⁻¹ • ((pDVRUnitK X) • (Integers (Kf X) : Set (Kf X))) := by
          rw [pDVRUnitK_smul_integers X]
    _ = (Integers (Kf X) : Set (Kf X)) := by
          rw [Units.smul_def, Units.smul_def, smul_smul,
            ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

theorem pDVRUnitK_inv_norm :
    ‖((pDVRUnitK X)⁻¹ : Kf X)‖ = 1 := by
  rw [norm_inv, pDVRUnitK_norm X, inv_one]

/-- Actual F-place uniformizer Haar character with the DVR data. -/
theorem distribHaarChar_uniformizer_at_F_actual
    (μ : Measure (Kf X)) [μ.IsAddHaarMeasure] [μ.Regular]
    (h0 : μ (Integers (Kf X) : Set (Kf X)) ≠ 0)
    (hfin : μ (Integers (Kf X) : Set (Kf X)) ≠ ∞) :
    distribHaarChar (Kf X) (chosenPiK X) =
      Real.toNNReal ((‖(chosenPiK X : Kf X)‖) ^
        (Module.finrank ℚ_[nativePrime X] (Kf X))) := by
  exact distribHaarChar_uniformizer_at_F (X := X) μ (chosenPiK X)
    (pDVRUnitK X)⁻¹ (fPlaceDVRUniformizerData X).exponent
    (fPlaceDVRUniformizerData X).exponent_ne_zero
    (pi_pow_eq_pUnit_unit_inv X) (pDVRUnitK_inv_smul_integers X)
    (pDVRUnitK_inv_norm X) h0 hfin

end LeanFormal.IUT.N8Closure.EtaUniformizerFieldRelationActual
