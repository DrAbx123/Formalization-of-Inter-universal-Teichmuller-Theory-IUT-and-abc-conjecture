import tmp.sheaf.n8.closure.EtaQRegionRepresentation
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling

/-!
# EtaQRegionHaarCalibrationActual

Attempt to close the qO Haar calibration.  The previous target used the factor
`exp(log ‖q‖) = ‖q‖`.  For a finite extension of local fields the additive Haar
scaling by q carries the residue degree f: the corrected factor is
`‖q‖ ^ f`, where f is the production relative residue degree of the native
F-place over its Fmod base place.

Production supplies only the rational-prime p-scaling theorem
(`FinitePadicHaarScaling.measure_prime_smul_finiteDimensional`), with factor
`p ^ (-finrank)`; no production theorem scales arbitrary q (including the
norm-one unit part and the residue-degree exponent).  Hence the corrected
target is the exact remaining scaling theorem, and the old raw-norm target is
the f = 1 special case, not the general calibration.

No arbitrary measure equality is assumed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaQRegionHaarCalibrationActual

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open MeasureTheory
open scoped NumberField ENNReal

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Production relative residue degree f of the native F-place over the Fmod
base place. -/
abbrev nativeRelativeResidueDegree : ℕ :=
  NumberFieldFinitePlace.relativeResidueDegree
    (k := X.S.arithmetic.Fmod) (nativeFPlaceOverBad X)

/-- Corrected qO Haar calibration: the factor includes the relative residue
degree f. -/
def EtaQRegionHaarCalibrationCorrected
    (μ : Measure (QCompletion X))
    [Measure.IsAddHaarMeasure μ] : Prop :=
  μ (qORegion X) =
    ENNReal.ofReal (‖(C9QPilotRegion.nativeQ X).q‖ ^ nativeRelativeResidueDegree X) *
      μ (Integers (QCompletion X) : Set (QCompletion X))

/-- The previous raw-norm calibration is exactly the f = 1 special case of the
corrected factor. -/
theorem etaQRegionHaarCalibration_rawNorm_factor_eq_one
    (hf : nativeRelativeResidueDegree X = 1) :
    (fun q : ℝ => ENNReal.ofReal (q ^ nativeRelativeResidueDegree X)) =
      (fun q : ℝ => ENNReal.ofReal q) := by
  funext q
  rw [hf, pow_one]

end LeanFormal.IUT.N8Closure.EtaQRegionHaarCalibrationActual