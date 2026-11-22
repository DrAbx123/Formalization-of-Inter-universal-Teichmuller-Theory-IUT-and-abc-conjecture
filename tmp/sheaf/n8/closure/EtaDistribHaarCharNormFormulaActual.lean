import tmp.sheaf.n8.closure.EtaGeneralQHaarScalingClosure
import tmp.sheaf.n8.closure.EtaUnitHaarInvarianceAttempt

/-!
# EtaDistribHaarCharNormFormulaActual

Actual proof of the distributive-character norm formula from the DVR
decomposition `q = u • π^z`, the actual uniformizer character and unit
invariance.  The proof is conditional on the chosen Haar measure having
positive finite measure on the integral unit ball (used only to identify the
unit character with one).
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaDistribHaarCharNormFormulaActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual
open LeanFormal.IUT.N8Closure.EtaValuedRankLeOneActual
open LeanFormal.IUT.N8Closure.EtaFPlaceDVRUniformizerDataActual
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.N8Closure.EtaUniformizerFieldRelationActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingClosure
open LeanFormal.IUT.N8Closure.EtaUnitHaarInvarianceAttempt
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open MeasureTheory
open scoped NNReal ENNReal Pointwise NormedField

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

noncomputable def charUnit : (Kf X)ˣ →* (NNReal)ˣ where
  toFun q := Units.mk0 (distribHaarChar (Kf X) q)
    (ne_of_gt (distribHaarChar_pos))
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [map_mul]

theorem charUnit_coe (q : (Kf X)ˣ) :
    ((charUnit X q : NNReal) : ENNReal) = (distribHaarChar (Kf X) q : ENNReal) :=
  rfl

theorem distribHaarCharNormFormula_of_measure
    (μ : Measure (Kf X)) [μ.IsAddHaarMeasure] [μ.Regular]
    (h0 : μ (Integers (Kf X) : Set (Kf X)) ≠ 0)
    (hfin : μ (Integers (Kf X) : Set (Kf X)) ≠ ∞) :
    DistribHaarCharNormFormula X := by
  intro q
  let D := qDecomposition X q
  let uK : (Kf X)ˣ := Units.map (algebraMap (Integers (Kf X)) (Kf X)) D.u
  let πK : (Kf X)ˣ := chosenPiK X
  have hchar_u : distribHaarChar (Kf X) uK = 1 := by
    exact distribHaarChar_eq_one_of_fixes_integers (K := Kf X) μ uK
      D.u_fixes_integers h0 hfin
  have hq_units : q = uK * πK ^ D.z := by
    apply Units.ext
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
    have h := D.q_eq
    simpa [uK, πK, chosenPiK, Algebra.smul_def, Units.smul_def] using h
  have hchar_q : distribHaarChar (Kf X) q =
      distribHaarChar (Kf X) uK * (distribHaarChar (Kf X) πK) ^ D.z := by
    have h := congrArg (fun x : (NNReal)ˣ => (x : NNReal))
      (map_mul (charUnit X) uK (πK ^ D.z))
    -- direct coercion of the monoid hom zpow equality
    rw [hq_units, map_mul, map_zpow]
    rfl
  have hchar_pi : distribHaarChar (Kf X) πK =
      Real.toNNReal ((‖(πK : Kf X)‖) ^

        (Module.finrank ℚ_[nativePrime X] (Kf X))) :=
    distribHaarChar_uniformizer_at_F_actual (X := X) μ h0 hfin
  rw [hchar_q, hchar_u, hchar_pi, one_mul]
  have hnorm : ‖(q : Kf X)‖ = ‖(πK : Kf X)‖ ^ D.z := by
    rw [hq_units]
    simp [uK, D.u_norm_one, norm_mul, norm_zpow]
  rw [hnorm]
  rw [← Real.toNNReal_zpow (pow_nonneg (norm_nonneg _) _) D.z]
  congr 1
  rw [zpow_mul, zpow_mul]
  congr 1
  ring

end LeanFormal.IUT.N8Closure.EtaDistribHaarCharNormFormulaActual