import tmp.sheaf.n8.closure.EtaComparisonVaryingTarget
import tmp.sheaf.n8.closure.C9PaperClosure
import tmp.sheaf.n8.closure.C9QPilotRegion
import tmp.sheaf.n8.closure.EtaRssNontrivialActual
import tmp.sheaf.n8.closure.EtaRssSourceRegionBridge
import Mathlib

/-!
# Eta varying calibration actual attempt

The paper output O = PaperC9Output X mu has:
- Q = QNamed X O.chainA = qPilotSignedLog X (actual q reduction);
- Theta = ThetaNamed O.theta = O.theta.ellOutValue, where O.theta.value is a
  donor-selected P6Readout value with only value_eq to ellOut.

O itself has no K/muK varying-region field and no source theorem identifying
Q or Theta with the varying-region open/closed readouts.  This file records the
exact reductions and the exact missing readout equalities.  No arbitrary
calibration is introduced.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.C9QThetaValuesNamed
open LeanFormal.IUT.N8Closure.C9PaperClosure
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaRssNontrivialActual
open LeanFormal.IUT.N8Closure.EtaRssSourceRegionBridge
open LeanFormal.IUT.N8Closure.EtaComparisonVaryingTarget

namespace LeanFormal.IUT.N8Closure.EtaVaryingCalibrationActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- O.Q reduces to the actual native q scalar; this is not yet the open-class
readout equality. -/
theorem Q_eq_nativeScalar (O : PaperC9Output (X := X) mu) :
    O.Q = qPilotSignedLog X :=
  O.Q_eq_nativeScalar

/-- O.Theta is the donor-selected readout value. -/
theorem Theta_eq_ellOutValue (O : PaperC9Output (X := X) mu) :
    O.Theta = O.theta.ellOutValue :=
  rfl

/-- Exact missing Q side: the actual native q scalar equals the varying-region
open-class readout.  This is an equality of actual quantities, not a free
calibration field. -/
def QOpenReadoutGap (K : Type u) [NormedField K] [MeasurableSpace K]
    [BorelSpace K] [IsUltrametricDist K] [ProperSpace K]
    (muK : Measure K) [Measure.IsAddHaarMeasure muK]
    (O : PaperC9Output (X := X) mu) : Prop :=
  qPilotSignedLog X =
    logVolumeReadout (K := K) (mu := muK) (sourceOpenClass (K := K) (mu := muK))

/-- Exact missing Theta side: the donor-selected Theta readout value equals the
varying-region closed-class readout. -/
def ThetaClosedReadoutGap (K : Type u) [NormedField K] [MeasurableSpace K]
    [BorelSpace K] [IsUltrametricDist K] [ProperSpace K]
    (muK : Measure K) [Measure.IsAddHaarMeasure muK]
    (O : PaperC9Output (X := X) mu) : Prop :=
  O.theta.ellOutValue =
    logVolumeReadout (K := K) (mu := muK) (sourceClosedClass (K := K) (mu := muK))

/-- Q calibration is equivalent to the exact Q readout gap. -/
theorem etaVaryingQCalibration_iff_QOpenReadoutGap
    (K : Type u) [NormedField K] [MeasurableSpace K] [BorelSpace K]
    [IsUltrametricDist K] [ProperSpace K] (muK : Measure K)
    [Measure.IsAddHaarMeasure muK]
    (O : PaperC9Output (X := X) mu) :
    EtaVaryingQCalibration (X := X) (mu := mu) K muK O ↔
      QOpenReadoutGap (X := X) (mu := mu) K muK O := by
  unfold EtaVaryingQCalibration QOpenReadoutGap
  rw [Q_eq_nativeScalar]

/-- Theta calibration is equivalent to the exact Theta readout gap. -/
theorem etaVaryingThetaCalibration_iff_ThetaClosedReadoutGap
    (K : Type u) [NormedField K] [MeasurableSpace K] [BorelSpace K]
    [IsUltrametricDist K] [ProperSpace K] (muK : Measure K)
    [Measure.IsAddHaarMeasure muK]
    (O : PaperC9Output (X := X) mu) :
    EtaVaryingThetaCalibration (X := X) (mu := mu) K muK O ↔
      ThetaClosedReadoutGap (X := X) (mu := mu) K muK O := by
  unfold EtaVaryingThetaCalibration ThetaClosedReadoutGap
  rw [Theta_eq_ellOutValue]

/-- Conditional consumer from the two exact source readout gaps. -/
theorem etaVarying_Q_le_Theta_of_sourceReadoutGaps
    (K : Type u) [NormedField K] [MeasurableSpace K] [BorelSpace K]
    [IsUltrametricDist K] [ProperSpace K] (muK : Measure K)
    [Measure.IsAddHaarMeasure muK]
    (O : PaperC9Output (X := X) mu)
    (hQ : QOpenReadoutGap (X := X) (mu := mu) K muK O)
    (hTheta : ThetaClosedReadoutGap (X := X) (mu := mu) K muK O) :
    O.Q ≤ O.Theta :=
  etaVarying_Q_le_Theta (X := X) (mu := mu) K muK O
    ((etaVaryingQCalibration_iff_QOpenReadoutGap (X := X) (mu := mu) K muK O).mpr hQ)
    ((etaVaryingThetaCalibration_iff_ThetaClosedReadoutGap (X := X) (mu := mu) K muK O).mpr hTheta)

end LeanFormal.IUT.N8Closure.EtaVaryingCalibrationActual
