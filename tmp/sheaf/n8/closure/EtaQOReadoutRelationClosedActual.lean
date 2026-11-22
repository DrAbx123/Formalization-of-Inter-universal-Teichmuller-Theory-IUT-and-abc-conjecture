import tmp.sheaf.n8.closure.EtaPreimageOQActual
import tmp.sheaf.n8.closure.EtaNormalizedHaarBothActual
import tmp.sheaf.n8.closure.EtaQOClassGlobalActual
import tmp.sheaf.n8.closure.EtaGlobalRegionAtFActual
import Mathlib.Topology.MetricSpace.Ultra.Basic
import tmp.sheaf.n8.closure.EtaPStepNormLink

/-!
# Close the qO readout relation

Both muQ and the pushed measure are actual normalized additive Haar measures on
QCompletion: muQ(O_Q)=1 and pushed(O_Q)=1.  Haar uniqueness (normalized at the
open integral ball O_Q) gives muQ = pushed on the actual qO region.  Hence the
qO class readouts agree.  No arbitrary measure equality is assumed.
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
open LeanFormal.IUT.N8Closure.EtaQOClassGlobalActual
open LeanFormal.IUT.N8Closure.EtaContinuousAddEquivRecordActual2
open LeanFormal.IUT.N8Closure.EtaPreimageOQActual
open LeanFormal.IUT.N8Closure.EtaNormalizedHaarBothActual
open LeanFormal.IUT.N8Closure.EtaQOReadoutRelationActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.N8Closure.EtaQOReadoutRelationClosedActual

local instance hKmeas : MeasurableSpace (EtaRssAdmissibleCorrection.K X) :=
  LeanFormal.IUT.N8Closure.EtaPStepNormLink.nativePMeasurableSpace X

local instance hKborel : BorelSpace (EtaRssAdmissibleCorrection.K X) :=
  LeanFormal.IUT.N8Closure.EtaPStepNormLink.nativePBorelSpace X

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [MeasurableSpace (QCompletion X)] [BorelSpace (QCompletion X)]
variable [ProperSpace (QCompletion X)] [IsUltrametricDist (QCompletion X)]
variable [LocallyCompactSpace (QCompletion X)]



/-- The actual qO region is open (closed ball in a nonarchimedean field). -/
theorem isOpen_qORegion : IsOpen (qORegion X) := by
  rw [qORegion_eq_closedBall X]
  exact IsUltrametricDist.isOpen_closedBall
    (x := (0 : QCompletion X)) (r := ‖(C9QPilotRegion.nativeQ X).q‖)
    (by exact norm_ne_zero_iff.mpr (C9QPilotRegion.nativeQ X).q_ne_zero)

/-- The integral-unit ball O_Q is open. -/
theorem isOpen_O_Q : IsOpen (EtaNormalizedHaarBothActual.O_Q X) := by
  change IsOpen (Integers (QCompletion X) : Set (QCompletion X))
  rw [show (Integers (QCompletion X) : Set (QCompletion X)) =
      Metric.closedBall (0 : QCompletion X) 1 by
    ext x
    rw [SetLike.mem_coe, mem_integers_iff, Metric.mem_closedBall, dist_zero_right]]
  exact IsUltrametricDist.isOpen_closedBall
    (x := (0 : QCompletion X)) (r := 1) (by norm_num)

/-- Both normalized Haar measures agree on the actual qO region. -/
theorem muQ_eq_pushed_on_qORegion :
    μQ X (qORegion X) = (pushed X) (qORegion X) := by
  haveI : (μQ X).IsAddHaarMeasure := by
    rw [μQ]
    exact Measure.IsAddHaarMeasure.smul _
      (ENNReal.inv_ne_zero.mpr (massQ_pos_lt_top X).2.ne)
      (ENNReal.inv_ne_top.mpr (massQ_pos_lt_top X).1.ne')
  haveI : (pushed X).IsAddHaarMeasure := pushed_isHaar X
  have hQ : (μQ X) (EtaNormalizedHaarBothActual.O_Q X) = 1 := μQ_O_Q X
  have hP : (pushed X) (EtaNormalizedHaarBothActual.O_Q X) = 1 := by
    have h := pushed_O_Q X
    rwa [show EtaContinuousAddEquivRecordActual2.O_Q X = EtaNormalizedHaarBothActual.O_Q X from rfl] at h
  have hposP : (pushed X).IsEverywherePos (qORegion X) :=
    (isOpen_qORegion X).isEverywherePos
  exact normalized_haar_agree_on_everywherePos (μQ X) (pushed X)
    (isOpen_O_Q X) hP hQ (isOpen_qORegion X).measurableSet hposP

/-- The qO class readouts of muQ and the pushed measure agree. -/
theorem qOClassReadout_muQ_eq_pushed
    [hμQ : (μQ X).IsAddHaarMeasure] [hp : (pushed X).IsAddHaarMeasure] :
    qOClassReadout X (μQ X) = qOClassReadout X (pushed X) := by
  rw [qOClassReadout_eq X (μQ X), qOClassReadout_eq X (pushed X)]
  rw [muQ_eq_pushed_on_qORegion X]

end LeanFormal.IUT.N8Closure.EtaQOReadoutRelationClosedActual
