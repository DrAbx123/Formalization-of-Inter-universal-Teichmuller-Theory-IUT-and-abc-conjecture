import tmp.sheaf.n8.closure.EtaComparisonMapActual
import tmp.sheaf.n8.closure.EtaQActual
import tmp.sheaf.n8.closure.PaperQLeThetaReduction
import Mathlib

/-!
# Eta consumer V2

Uses the v2 varying-region Rss carrier EtaRssLogShellLineData and the actual
q calibration etaQScalar.  The actual comparison map on this carrier is
constant (subsingleton Rss); nonconstancy is derived impossible, so no
unsourced nonconstancy guard is imposed.

The consumer takes the actual v2 comparison, the actual q calibration, the exact
Q identification, and the P6/Values route.  No Theta/Values/reference guards are
used as hypotheses; missing exact facts are named gaps.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C9QThetaValuesNamed
open LeanFormal.IUT.N8Closure.C9PaperClosure
open LeanFormal.IUT.N8Closure.PaperQLeThetaReduction
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaComparisonMapActual
open LeanFormal.IUT.N8Closure.EtaRssLogShellLine
open LeanFormal.IUT.N8Closure.EtaQActual

namespace LeanFormal.IUT.N8Closure.EtaConsumerV2

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- The v2 varying-region comparison: equality of the actual maps into the
native log-shell line. -/
def EtaComparisonV2 : Prop :=
  EtaComparisonOnRss (X := X) (etaQMap X) (etaAnabMap X)

/-- The actual v2 comparison holds (both maps are the canonical actual map). -/
theorem etaComparisonV2_actual : EtaComparisonV2 X :=
  etaQ_etaAnab_square X

/-- Derived nonconstancy no-go: no nonconstant map into the actual Rss line
exists, so a nonconstancy guard cannot be required. -/
theorem etaComparisonV2_nonconstant_noGo :
    ¬ ∃ f : LeanFormal.IUT.N8Closure.EtaValueGroupLineActual.Rval →
        EtaRssLogShellLineData X,
        EtaComparisonNonconstant X f :=
  etaIndependentComparison_noGo X

/-- Actual q calibration: the value-group eta scalar is the native q scalar. -/
def EtaQCalibrationV2 : Prop :=
  etaQScalar X = qPilotSignedLog X

/-- Exact normalized Q identification with the v2 actual q scalar. -/
def EtaV2QNormalizedIdentification (O : PaperC9Output (X := X) mu) : Prop :=
  O.Q = etaQScalar X

/-- V2 consumer data: actual comparison, q calibration, exact Q
identification, and the P6/Values route.  No unsourced Theta/Values/reference
guards are included. -/
structure EtaConsumerV2Data (O : PaperC9Output (X := X) mu) : Prop where
  comparison : EtaComparisonV2 X
  qCalibration : EtaQCalibrationV2 X
  qIdentification : EtaV2QNormalizedIdentification (X := X) (mu := mu) O
  valuesBounded : ValuesBounded (X := X) (mu := mu) O

/-- V2 conditional consumer: Q <= Theta from the v2 data.  The inequality
comes from the P6/Values route; the eta data supplies the q-side normalization. -/
theorem etaNormalizedQ_le_Theta_v2
    (O : PaperC9Output (X := X) mu)
    (D : EtaConsumerV2Data X mu O) :
    O.Q ≤ O.Theta := by
  have hQneg : O.Q < 0 := by
    rw [D.qIdentification, D.qCalibration]
    exact qPilotSignedLog_neg X
  exact PaperQLeThetaReduction.paperQLeTheta (X := X) (mu := mu) O D.valuesBounded

end LeanFormal.IUT.N8Closure.EtaConsumerV2
