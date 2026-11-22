import tmp.sheaf.n8.closure.EtaGeneralQHaarScalingClosure

/-!
# EtaDistribHaarCharNormFormulaActual2

Partial closure.  Blocker (1) is solved: `distribHaarChar` (a monoid hom
into `ℝ≥0`) is packaged as a monoid hom into `(ℝ≥0)ˣ` using positivity, so
`map_zpow` applies to the actual decomposition `q = u * π^z`.

Blocker (2) remains: identifying the packaged unit character of the DVR unit
with `1` requires the measure-dependent unit-invariance lemma.  The formula
itself is recorded as the exact remaining target.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaDistribHaarCharNormFormulaActual2

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual
open LeanFormal.IUT.N8Closure.EtaFPlaceDVRUniformizerDataActual
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingClosure
open LeanFormal.IUT.N8Closure.EtaUniformizerFieldRelationActual
open MeasureTheory
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

/-- Positive char values packaged as units of `ℝ≥0`. -/
noncomputable def charUnit : (Kf X)ˣ →* (NNReal)ˣ where
  toFun q := Units.mk0 (distribHaarChar (Kf X) q)
    (ne_of_gt (distribHaarChar_pos))
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [map_mul]

theorem charUnit_coe (q : (Kf X)ˣ) :
    (charUnit X q : NNReal) = distribHaarChar (Kf X) q := rfl

end LeanFormal.IUT.N8Closure.EtaDistribHaarCharNormFormulaActual2