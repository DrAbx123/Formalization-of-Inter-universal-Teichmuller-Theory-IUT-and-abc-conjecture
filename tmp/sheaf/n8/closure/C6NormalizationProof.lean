import tmp.sheaf.n8.closure.SourceHolomorphicHull
import tmp.sheaf.n8.closure.C6ActualIQData
import Mathlib

/-!
# C6 actual normalization bridge

This file writes the actual relations between C6ActualIQData's normalized and
signed Haar data and the C7 IQ interface log-volume. It is a stage-3 bridge:
the conditional equalities below are proved from the C6/C7 definitions, while
the identification of an arbitrary C6ActualIQData field with the actual donor
is kept as an explicit hypothesis (the actual instance satisfies it by
definition). No product-of-fields data is used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C6Normalization

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open ABCBridge.N8.C4Actual
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open LeanFormal.IUT.N8Closure.SourceThetaToIQ

universe ua uv upi umon ui uL uG

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C1 : SourceInputBinding I) (C2 : SourceLogKummerData I C1)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (D : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))
variable (C5 : SourceAlgorithmCompatibilityData I C1 C2 C3 D)
variable [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple))
variable [Measure.IsAddHaarMeasure mu]
variable (B : C6ActualIQData C3.tensorPlaces C3.tensorTuple mu)
variable (T : SourceThetaIQInterface (I := I) C3)

/-- The C8 iqMuLog: the real part of the C7 IQ hull log-volume. -/
def iqMuLog : ℝ :=
  (B.iqInterface.logVolume (commonHull (C3 := C3) mu B)).toReal

/-- Exact sign relation: iqMuLog is the nonnegative part of the signed hull
log when the C6 actual data are used. The ENNReal.toReal in iqMuLog is
sign-blind; this is the exact place where the sign is lost. -/
theorem iqMuLog_eq_max_signedHullLog
    (hlog : B.iqInterface.logVolume = haarLogVolume mu)
    (hhull : commonHull (C3 := C3) mu B =
      arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple)
    (hsigned : B.signedHullLog =
      arithmeticTupleCanonicalHullHaarLog C3.tensorPlaces C3.tensorTuple mu)
    (hfin : mu (arithmeticTupleCanonicalHull
      C3.tensorPlaces C3.tensorTuple) < ⊤) :
    iqMuLog (C3 := C3) mu B = max B.signedHullLog 0 := by
  unfold iqMuLog
  rw [hhull, hlog, hsigned, arithmeticTupleCanonicalHullHaarLog,
    haarLogVolume_of_lt_top hfin]
  exact ENNReal.toReal_ofReal'

/-- Exact normalized-volume formula: the C6 normalized log-volume is the
normalization weight times the log-ratio of the region and the actual unit
reference. -/
theorem normalizedLogVolume_eq_normalization_mul_log_ratio
    (hnorm : B.normalizedLogVolume =
      arithmeticTupleNormalizedLogVolume C3.tensorPlaces C3.tensorTuple mu)
    (hweight : B.normalizationWeight =
      1 / (Module.finrank ℚ_[C3.p]
        (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple) : ℝ))
    (hunit : B.unitReferenceLog =
      Real.log (mu (arithmeticTupleCanonicalUnitReference
        C3.tensorPlaces C3.tensorTuple)).toReal)
    (S : Set (C6IQCarrier C3.tensorPlaces C3.tensorTuple)) :
    B.normalizedLogVolume S =
      B.normalizationWeight *
        (Real.log (mu S).toReal - B.unitReferenceLog) := by
  rw [hnorm, hweight, hunit, arithmeticTupleNormalizedLogVolume]

/-- On the actual common hull, the normalized log-volume is the normalization
weight times signed hull log minus the unit-reference log. -/
theorem normalizedLogVolume_commonHull_eq_weight_mul_signedHullLog_sub_unit
    (hnorm : B.normalizedLogVolume =
      arithmeticTupleNormalizedLogVolume C3.tensorPlaces C3.tensorTuple mu)
    (hweight : B.normalizationWeight =
      1 / (Module.finrank ℚ_[C3.p]
        (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple) : ℝ))
    (hunit : B.unitReferenceLog =
      Real.log (mu (arithmeticTupleCanonicalUnitReference
        C3.tensorPlaces C3.tensorTuple)).toReal)
    (hhull : commonHull (C3 := C3) mu B =
      arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple)
    (hsigned : B.signedHullLog =
      arithmeticTupleCanonicalHullHaarLog C3.tensorPlaces C3.tensorTuple mu) :
    B.normalizedLogVolume (commonHull (C3 := C3) mu B) =
      B.normalizationWeight * (B.signedHullLog - B.unitReferenceLog) := by
  rw [normalizedLogVolume_eq_normalization_mul_log_ratio
    (C3 := C3) (mu := mu) B hnorm hweight hunit, hhull, hsigned,
    arithmeticTupleCanonicalHullHaarLog]

/-- Interface form: the C7 hull log-volume and C6 normalized data determine
each other through the normalization weight and the unit-reference log. -/
theorem iqMuLog_eq_signedHullLog_of_nonneg
    (hlog : B.iqInterface.logVolume = haarLogVolume mu)
    (hhull : commonHull (C3 := C3) mu B =
      arithmeticTupleCanonicalHull C3.tensorPlaces C3.tensorTuple)
    (hsigned : B.signedHullLog =
      arithmeticTupleCanonicalHullHaarLog C3.tensorPlaces C3.tensorTuple mu)
    (hfin : mu (arithmeticTupleCanonicalHull
      C3.tensorPlaces C3.tensorTuple) < ⊤)
    (hnonneg : 0 ≤ B.signedHullLog) :
    iqMuLog (C3 := C3) mu B = B.signedHullLog := by
  rw [iqMuLog_eq_max_signedHullLog (C3 := C3) (mu := mu) B hlog hhull hsigned hfin,
    max_eq_left hnonneg]

end LeanFormal.IUT.N8Closure.C6Normalization
