import tmp.sheaf.n8.closure.EtaGeneralQHaarScalingActual
import tmp.sheaf.n8.closure.EtaUnitHaarInvarianceAttempt

/-!
# EtaGeneralQHaarScalingClosure

Actual reduction of the general-q Haar scaling to the distributive-character
norm formula.  The qO region is the scalar action on the integral unit ball,
and `distribHaarChar_mul` gives the measure identity once
`char(q) = toNNReal(‖q‖^d)` is known.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingClosure

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual
open LeanFormal.IUT.N8Closure.EtaValuedRankLeOneActual
open LeanFormal.IUT.N8Closure.EtaFPlaceDVRUniformizerDataActual
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.N8Closure.EtaUniformizerFieldRelationActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open MeasureTheory
open scoped NNReal ENNReal Pointwise NormedField

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

theorem qORegion_eq_smul (q : (Kf X)ˣ) :
    qORegion X (q : Kf X) = q • (Integers (Kf X) : Set (Kf X)) := by
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, y.property, by simp [Units.smul_def]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, by simp [Units.smul_def]⟩

/-- Exact distributive-character norm formula. -/
def DistribHaarCharNormFormula (X : N8NativeInput l) : Prop :=
  ∀ q : (Kf X)ˣ,
    distribHaarChar (Kf X) q =
      Real.toNNReal ((‖(q : Kf X)‖) ^

        (Module.finrank ℚ_[nativePrime X] (Kf X)))

/-- Actual measure identity from the char formula. -/
theorem generalQHaarScalingTarget_of_charFormula
    (hchar : DistribHaarCharNormFormula X)
    (μ : Measure (Kf X)) [μ.IsAddHaarMeasure] [μ.Regular]
    (h0 : μ (Integers (Kf X) : Set (Kf X)) ≠ 0)
    (hfin : μ (Integers (Kf X) : Set (Kf X)) ≠ ∞) :
    GeneralQHaarScalingTarget X μ := by
  intro q
  rw [qORegion_eq_smul X q]
  have hmul := distribHaarChar_mul (A := Kf X) (μ := μ) q
    (Integers (Kf X) : Set (Kf X))
  rw [hchar q] at hmul
  rw [← hmul]
  rw [ENNReal.ofNNReal_toNNReal]

end LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingClosure