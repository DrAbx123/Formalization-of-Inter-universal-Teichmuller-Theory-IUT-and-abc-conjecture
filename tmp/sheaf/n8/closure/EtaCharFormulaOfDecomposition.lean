import tmp.sheaf.n8.closure.EtaDistribHaarCharNormFormulaActual3
import tmp.sheaf.n8.closure.EtaGeneralQHaarScalingClosure
import tmp.sheaf.n8.closure.EtaFPlaceDVRUniformizerDataActual

/-!
# EtaCharFormulaOfDecomposition

Prove the char norm formula from a free decomposition
`q = u * π^z`, rewriting only the free variable `q`.  Then instantiate with
the actual `qDecomposition`.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaCharFormulaOfDecomposition

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open MeasureTheory
open scoped NNReal ENNReal Pointwise NormedField

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Q := EtaGeneralQHaarScalingActual.Kf X

noncomputable def charUnit : (Q X)ˣ →* (NNReal)ˣ where
  toFun q := Units.mk0 (distribHaarChar (Q X) q)
    (ne_of_gt (distribHaarChar_pos))
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [map_mul]

theorem charUnit_coe (q : (Q X)ˣ) :
    (charUnit X q : NNReal) = distribHaarChar (Q X) q := rfl

theorem char_formula_of_decomposition
    (q : (Q X)ˣ) (z : ℤ) (u : (Integers (Q X))ˣ)
    (hqval : (q : Q X) = (u : Q X) *
      (EtaUniformizerFieldRelationActual.chosenPiK X : Q X) ^ z) :
    distribHaarChar (Q X) q =
      Real.toNNReal ((‖(q : Q X)‖) ^
        (Module.finrank ℚ_[nativePrime X] (Q X))) := by
  let uK : (Q X)ˣ := Units.map (algebraMap (Integers (Q X)) (Q X)) u
  let πK : (Q X)ˣ := EtaUniformizerFieldRelationActual.chosenPiK X
  have hq_units : q = uK * πK ^ z := by
    apply Units.ext
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val]
    change (q : Q X) = (↑↑u : Q X) *
      (↑(EtaUniformizerFieldRelationActual.chosenPiK X) : Q X) ^ z
    exact hqval
  have h0 : (Measure.addHaar : Measure (Q X)) (Integers (Q X) : Set (Q X)) ≠ 0 :=
    (EtaDistribHaarCharNormFormulaActual3.addHaar_O_pos X).ne'
  have hfin : (Measure.addHaar : Measure (Q X)) (Integers (Q X) : Set (Q X)) ≠ ∞ :=
    (EtaDistribHaarCharNormFormulaActual3.addHaar_O_finite X).ne
  have huO : uK • (Integers (Q X) : Set (Q X)) = (Integers (Q X) : Set (Q X)) := by
    simpa [uK] using EtaFPlaceDVRUniformizerDataActual.integersUnit_smul_integers (X := X) u
  have hu_norm : ‖(uK : Q X)‖ = 1 := by
    change ‖((u : Integers (Q X)) : Q X)‖ = 1
    exact Valued.integer.norm_coe_unit u
  have hchar_u : distribHaarChar (Q X) uK = 1 :=
    EtaUniformizerHaarCharActual.distribHaarChar_eq_one_of_fixes_integers
      (K := Q X) (Measure.addHaar : Measure (Q X)) uK huO h0 hfin
  have hchar_pi : distribHaarChar (Q X) πK =
      Real.toNNReal ((‖(πK : Q X)‖) ^
        (Module.finrank ℚ_[nativePrime X] (Q X))) :=
    EtaUniformizerFieldRelationActual.distribHaarChar_uniformizer_at_F_actual
      (X := X) (Measure.addHaar : Measure (Q X)) h0 hfin
  have hchar_q : distribHaarChar (Q X) q =
      distribHaarChar (Q X) uK * (distribHaarChar (Q X) πK) ^ z := by
    have hhom : charUnit X q = charUnit X uK * (charUnit X πK) ^ z := by
      rw [hq_units, map_mul, map_zpow]
    have h := congrArg (fun x : (NNReal)ˣ => (x : NNReal)) hhom
    simpa [charUnit, Units.val_mul, Units.val_zpow_eq_zpow_val] using h
  rw [hchar_q, hchar_u, hchar_pi, one_mul]
  have hnorm : ‖(q : Q X)‖ = ‖(πK : Q X)‖ ^ z := by
    rw [hq_units, Units.val_mul, Units.val_zpow_eq_zpow_val, norm_mul, norm_zpow,
      hu_norm, one_mul]
  rw [hnorm]
  rw [← Real.toNNReal_zpow (pow_nonneg (norm_nonneg _) _) z]
  congr 1
  rw [show (‖(πK : Q X)‖ ^ Module.finrank ℚ_[nativePrime X] (Q X) : ℝ)
      = ‖(πK : Q X)‖ ^ ((Module.finrank ℚ_[nativePrime X] (Q X) : ℕ) : ℤ) by
    rw [zpow_natCast]]
  rw [← zpow_mul]
  rw [show (‖(πK : Q X)‖ ^ z : ℝ) ^ (Module.finrank ℚ_[nativePrime X] (Q X))
      = (‖(πK : Q X)‖ ^ z) ^ ((Module.finrank ℚ_[nativePrime X] (Q X) : ℕ) : ℤ) by
    rw [zpow_natCast]]
  rw [← zpow_mul']

end LeanFormal.IUT.N8Closure.EtaCharFormulaOfDecomposition