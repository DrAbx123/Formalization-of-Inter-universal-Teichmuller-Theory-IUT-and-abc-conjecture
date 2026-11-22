import tmp.sheaf.n8.closure.EtaGlobalRssAtF
import tmp.sheaf.n8.closure.EtaGlobalRegionAtFActual
import Mathlib

/-!
# Actual global qO class in GlobalRssAtF

Bypasses the FLevelGlobalClassBridge: using the canonical GlobalRssAtF
carrier/measure, we take the actual qO region (= closed ball of radius ||q||,
positive finite) directly in the F-level quotient, define globalQOClass and its
log-volume readout, and record the exact remaining measure/readout relation with
the multiradial qOClass.  No arbitrary quotient map is introduced.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaGlobalRegionAtFActual
open LeanFormal.IUT.N8Closure.EtaAnabAtFPlace
open LeanFormal.IUT.N8Closure.EtaRssAdmissibleCorrection
open LeanFormal.IUT.N8Closure.EtaGlobalRssAtF

namespace LeanFormal.IUT.N8Closure.EtaQOClassGlobalActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [MeasurableSpace (K X)] [BorelSpace (K X)]
variable (μK : Measure (K X)) [Measure.IsAddHaarMeasure μK]
variable [Measure.IsOpenPosMeasure μK] [IsFiniteMeasureOnCompacts μK]
variable [ProperSpace (K X)] [IsUltrametricDist (K X)]
variable [NormedSpace ℚ_[FPlacePrime X] (K X)]
variable [FiniteDimensional ℚ_[FPlacePrime X] (K X)]
variable [Nontrivial (K X)]
variable [NormSMulClass ℚ_[FPlacePrime X] (K X)]

variable [MeasurableSpace (QCompletion X)] [BorelSpace (QCompletion X)]
variable [ProperSpace (QCompletion X)] [IsUltrametricDist (QCompletion X)]
variable (μQ : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μQ]

/-- Actual qO region at the F carrier, in its closed-ball form. -/
def globalQOCarrier : Set (K X) :=
  Metric.closedBall (0 : K X) ‖(C9QPilotRegion.nativeQ X).q‖

/-- Actual positive finite qO region in GlobalRssAtF. -/
def globalQOAdmissible : AdmissibleRegion (X := X) (mu := μK) where
  carrier := globalQOCarrier X
  measurable := measurableSet_closedBall
  pos := Metric.measure_closedBall_pos μK 0 (nativeQ_norm_pos X)
  finite := (isCompact_closedBall (0 : K X) _).measure_lt_top

/-- Actual global qO class in GlobalRssAtF. -/
noncomputable def globalQOClass : Rss (X := X) (mu := μK) :=
  rssOf (X := X) (mu := μK) (globalQOAdmissible X μK)

/-- Actual global qO readout. -/
noncomputable def globalQOReadout : ℝ :=
  Real.log ((readout (X := X) (mu := μK) (globalQOClass X μK)).toReal)

theorem globalQOReadout_eq :
    globalQOReadout (X := X) (μK := μK) =
      Real.log (μK (globalQOCarrier X)).toReal := by
  rfl

/-- Exact remaining relation with the multiradial qOClass readout: it is the
measure agreement on the qO region / readout comparison.  Not assumed; this is
the exact gap. -/
def QOReadoutRelationTarget : Prop :=
  globalQOReadout (X := X) (μK := μK) = qOClassReadout X μQ

/-- Conditional relation: if the global and multiradial measures agree on the
actual qO region, the readouts agree. -/
theorem globalQOReadout_eq_qOClassReadout
    (h : μK (globalQOCarrier X) = μQ (qORegion X)) :
    globalQOReadout (X := X) (μK := μK) = qOClassReadout X μQ := by
  rw [globalQOReadout_eq, qOClassReadout_eq]
  exact congrArg (fun z : ENNReal => Real.log z.toReal) h

end LeanFormal.IUT.N8Closure.EtaQOClassGlobalActual
