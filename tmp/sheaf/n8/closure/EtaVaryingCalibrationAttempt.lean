import tmp.sheaf.n8.closure.EtaVaryingCalibrationActual
import tmp.sheaf.n8.closure.C9QPilotRegion
import tmp.sheaf.n8.closure.EtaRssNontrivialActual
import Mathlib

/-!
# Eta varying calibration attempt

Actual computations for the two exact gaps:

  Q gap:     qPilotSignedLog X = log(muK openRegion)
  Theta gap: O.theta.value = log(muK closedRegion)

The reductions are proved from the actual definitions.  No source equation
identifies the native q scalar or the donor-selected P6Readout.value with these
external varying-region masses; the missing source equations are recorded
exactly.  No arbitrary calibration is introduced.
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
open LeanFormal.IUT.N8Closure.EtaVaryingCalibrationActual

namespace LeanFormal.IUT.N8Closure.EtaVaryingCalibrationAttempt

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

variable (K : Type u) [NormedField K] [MeasurableSpace K] [BorelSpace K]
  [IsUltrametricDist K] [ProperSpace K]
variable (muK : Measure K) [Measure.IsAddHaarMeasure muK]
variable (O : PaperC9Output (X := X) mu)

/-- Actual q computation. -/
theorem qPilotSignedLog_computation :
    qPilotSignedLog X =
      ArithmeticQPilotLogVolume.localSignedLog (nativeQ X) :=
  rfl

/-- The open-class readout is the log of the actual open ball mass. -/
theorem openReadout_eq_log_mass :
    logVolumeReadout (K := K) (mu := muK)
        (sourceOpenClass (K := K) (mu := muK)) =
      Real.log (muK (openRegion (K := K) (mu := muK)).carrier).toReal := by
  rw [sourceOpenClass, sourceOpenRegion, logVolumeReadout_mk]

/-- The closed-class readout is the log of the actual closed ball mass. -/
theorem closedReadout_eq_log_mass :
    logVolumeReadout (K := K) (mu := muK)
        (sourceClosedClass (K := K) (mu := muK)) =
      Real.log (muK (closedRegion (K := K) (mu := muK)).carrier).toReal := by
  rw [sourceClosedClass, sourceClosedRegion, logVolumeReadout_mk]

/-- Exact source equation needed for the Q calibration. -/
def MissingQSourceEquation : Prop :=
  ArithmeticQPilotLogVolume.localSignedLog (nativeQ X) =
    Real.log (muK (openRegion (K := K) (mu := muK)).carrier).toReal

/-- Exact source equation needed for the Theta calibration. -/
def MissingThetaSourceEquation : Prop :=
  O.theta.ellOutValue =
    Real.log (muK (closedRegion (K := K) (mu := muK)).carrier).toReal

/-- The Q calibration gap is exactly the missing Q source equation. -/
theorem qOpenReadoutGap_iff_missingQSource :
    QOpenReadoutGap (X := X) (mu := mu) K muK O ↔
      MissingQSourceEquation (X := X) K muK := by
  unfold QOpenReadoutGap MissingQSourceEquation
  rw [openReadout_eq_log_mass, qPilotSignedLog_eq_localSignedLog]

/-- The Theta calibration gap is exactly the missing Theta source equation. -/
theorem thetaClosedReadoutGap_iff_missingThetaSource :
    ThetaClosedReadoutGap (X := X) (mu := mu) K muK O ↔
      MissingThetaSourceEquation (X := X) (mu := mu) K muK O := by
  unfold ThetaClosedReadoutGap MissingThetaSourceEquation
  rw [closedReadout_eq_log_mass]

/-- Decisive no-go form: the two calibrations are equivalent to the two
external mass equations above.  No existing theorem supplies either; O has no
K/muK varying-region field and P6Readout.value is donor-selected. -/
theorem calibrations_are_external_mass_equations :
    (EtaVaryingQCalibration (X := X) (mu := mu) K muK O ↔
        MissingQSourceEquation (X := X) K muK) ∧
      (EtaVaryingThetaCalibration (X := X) (mu := mu) K muK O ↔
        MissingThetaSourceEquation (X := X) (mu := mu) K muK O) :=
  ⟨(etaVaryingQCalibration_iff_QOpenReadoutGap (X := X) (mu := mu) K muK O).trans
      (qOpenReadoutGap_iff_missingQSource (X := X) (mu := mu) K muK O),
    (etaVaryingThetaCalibration_iff_ThetaClosedReadoutGap (X := X) (mu := mu) K muK O).trans
      (thetaClosedReadoutGap_iff_missingThetaSource (X := X) (mu := mu) K muK O)⟩

end LeanFormal.IUT.N8Closure.EtaVaryingCalibrationAttempt
