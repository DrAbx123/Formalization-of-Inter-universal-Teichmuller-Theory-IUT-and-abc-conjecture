import tmp.sheaf.n8.closure.EtaCharFormulaOfDecomposition

/-!
# EtaCharFormulaInstantiation

Explicit coercion lemmas converting the actual `qDecomposition` smul form
`D.u • algebraMap π^z` into the product form used by
`char_formula_of_decomposition`, then instantiate the general formula.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaCharFormulaInstantiation

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

theorem integerUnit_smul_eq_algebraMap_mul
    (u : (Integers (Q X))ˣ) (y : Q X) :
    u • y = (algebraMap (Integers (Q X)) (Q X)) (u : Integers (Q X)) * y := by
  rw [Units.smul_def, Algebra.smul_def]

theorem units_coe_eq_algebraMap (u : (Integers (Q X))ˣ) :
    (u : Q X) = (algebraMap (Integers (Q X)) (Q X)) (u : Integers (Q X)) := rfl

theorem chosenPiK_coe_eq_algebraMap :
    (EtaUniformizerFieldRelationActual.chosenPiK X : Q X) =
      (algebraMap (Integers (Q X)) (Q X))
        (EtaFPlaceDVRUniformizerDataActual.fPlaceDVRUniformizerData X).pi := rfl

theorem distribHaarCharNormFormula_actual :
    EtaGeneralQHaarScalingClosure.DistribHaarCharNormFormula X := by
  intro q
  let D := EtaGeneralQHaarScalingActual.qDecomposition X q
  have hqval : (q : Q X) = (D.u : Q X) *
      (EtaUniformizerFieldRelationActual.chosenPiK X : Q X) ^ D.z := by
    rw [units_coe_eq_algebraMap, chosenPiK_coe_eq_algebraMap]
    have h := D.q_eq
    rw [integerUnit_smul_eq_algebraMap_mul] at h
    exact h
  exact EtaCharFormulaOfDecomposition.char_formula_of_decomposition X q D.z D.u hqval

theorem generalQHaarScalingTarget_actual :
    EtaGeneralQHaarScalingActual.GeneralQHaarScalingTarget X
      (Measure.addHaar : Measure (Q X)) :=
  EtaGeneralQHaarScalingClosure.generalQHaarScalingTarget_of_charFormula X
    (distribHaarCharNormFormula_actual X) (Measure.addHaar : Measure (Q X))
    (EtaDistribHaarCharNormFormulaActual3.addHaar_O_pos X).ne'
    (EtaDistribHaarCharNormFormulaActual3.addHaar_O_finite X).ne

end LeanFormal.IUT.N8Closure.EtaCharFormulaInstantiation