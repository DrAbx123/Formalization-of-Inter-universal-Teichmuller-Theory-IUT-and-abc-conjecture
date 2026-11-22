import tmp.sheaf.xif.paper.SourceHullVolumeSignCorrectedActual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual

/-! # Corrected positive Theta hull log-volume vs native q-pilot

Uses the sign-corrected actual positive hull log-volume of
SourceHullVolumeSignCorrectedActual:

  positiveHullLogVolume v R n
    = sup over actual sourceHolomorphicHull of
        ENNReal.ofReal (positivePointLogVolume v x),

where positivePointLogVolume v x = -sourceLocalLogDegree v x.

This is NOT the old sourcePointVolume: the old one is
ENNReal.ofReal (sourceLocalLogDegree) and truncates the negative theta log to
zero.

The corrected comparison is defined at the scalar level with the actual native
q-pilot normalized magnitude:

  positiveHullLogVolumeReal <= nativeGlobalQPilotNormalizedLogMagnitude,

and the signed version

  -nativeGlobalQPilotNormalizedLogMagnitude
    <= -positiveHullLogVolumeReal.

The inequalities are Prop definitions only; no inequality is proved or assumed.
No old zero volume, no object equality, no carrier equivalence.  No
sorry/axiom. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PositiveHullVsQPilotCorrectedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.OriginalInput.SourceHullVolumeSignCorrectedActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v)
variable (n : ThetaPilotCarrier l)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Actual corrected positive hull log-volume as a real scalar. -/
noncomputable def positiveHullLogVolumeReal : Real :=
  (positiveHullLogVolume I v R n).toReal

/-- The corrected positive hull log-volume is exactly the sup of positive point
log-volumes over the actual holomorphic hull. -/
theorem positiveHullLogVolumeReal_eq :
    positiveHullLogVolumeReal I v R n =
      (⨆ x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        ENNReal.ofReal (positivePointLogVolume (I := I) v x)).toReal :=
  rfl

/-- Actual native q-pilot normalized magnitude. -/
noncomputable def nativeQPilotNormalizedMagnitude
    (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))] : Real :=
  nativeGlobalQPilotNormalizedLogMagnitude T

/-- Corrected positive hull magnitude is at most the native q-pilot normalized
magnitude. -/
def PositiveHullVsQPilotCorrected
    (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))] : Prop :=
  positiveHullLogVolumeReal I v R n ≤ nativeQPilotNormalizedMagnitude T

/-- Signed version of the corrected comparison. -/
def PositiveHullVsQPilotCorrectedSigned
    (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))] : Prop :=
  -nativeQPilotNormalizedMagnitude T ≤ -positiveHullLogVolumeReal I v R n

/-- The signed corrected comparison is exactly the positive one. -/
theorem positiveHullVsQPilotCorrectedSigned_iff :
    PositiveHullVsQPilotCorrectedSigned I v R n T ↔
      PositiveHullVsQPilotCorrected I v R n T := by
  unfold PositiveHullVsQPilotCorrectedSigned PositiveHullVsQPilotCorrected
  constructor <;> intro h <;> linarith

/-- Actual corrected comparison data. -/
structure PositiveHullVsQPilotCorrectedData
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] where
  positiveHull : Real
  positiveHull_eq : positiveHull = positiveHullLogVolumeReal I v R n
  qPilotNormalized : Real
  qPilotNormalized_eq : qPilotNormalized = nativeQPilotNormalizedMagnitude T
  comparison : Prop
  comparison_eq : comparison = (positiveHull ≤ qPilotNormalized)

/-- The actual corrected comparison data from the two actual scalars. -/
noncomputable def positiveHullVsQPilotCorrectedData :
    PositiveHullVsQPilotCorrectedData I v R n T where
  positiveHull := positiveHullLogVolumeReal I v R n
  positiveHull_eq := rfl
  qPilotNormalized := nativeQPilotNormalizedMagnitude T
  qPilotNormalized_eq := rfl
  comparison := PositiveHullVsQPilotCorrected I v R n T
  comparison_eq := rfl

/-- Conditional theorem surface: the corrected comparison follows only from an
explicit scalar hypothesis, not from a fake inequality. -/
theorem positiveHullLeQPilot_of_hypothesis
    (h : positiveHullLogVolumeReal I v R n ≤ nativeQPilotNormalizedMagnitude T) :
    PositiveHullVsQPilotCorrected I v R n T :=
  h

end LeanFormal.IUT.XiFPaper.PositiveHullVsQPilotCorrectedActual

end
