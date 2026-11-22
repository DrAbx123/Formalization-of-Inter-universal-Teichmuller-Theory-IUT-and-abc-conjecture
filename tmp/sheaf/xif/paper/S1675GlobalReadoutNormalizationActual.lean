import tmp.sheaf.xif.paper.GlobalHullSignedComparisonActual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.GlobalThetaHullVsQPilotComparisonActual

noncomputable section
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1675GlobalReadoutNormalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotHullLogVolumeActual
open LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.GlobalHullSignedComparisonActual

universe ua uv upi umon ui u

variable {l : PrimeGeFive} {V : Type uv}
variable [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : forall v : V, I.SourceImageRealization v)
variable (n : ThetaPilotCarrier l)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Exact first source normalization: the single one-column q-pilot signed
scalar is the native per-b weighted q-pilot normalized signed scalar. -/
def S1675OneColumnNormalization : Prop :=
  I.qPilotSignedLogVolume =
    nativeGlobalQPilotNormalizedSignedLogVolume (T := T)

/-- Exact hull readout bound: the actual global theta hull log-volume is at
most the native weighted q-pilot magnitude. -/
def S1675HullNativeMagnitudeBound : Prop :=
  globalThetaHullLogVolume (I := I) R n <=
    nativeGlobalQPilotNormalizedLogMagnitude (T := T)

/-- The exact first missing normalization/readout package. -/
structure S1675GlobalReadoutNormalizationData where
  one_column_eq : S1675OneColumnNormalization (I := I) T
  hull_bound : S1675HullNativeMagnitudeBound (I := I) R n T

/-- Conditional actual: the one-column normalization identifies the q-pilot
magnitude with the native weighted q magnitude. -/
theorem s1675QPilotMagnitude_eq_native
    (h : S1675OneColumnNormalization (I := I) T) :
    qPilotMagnitude (I := I) =
      nativeGlobalQPilotNormalizedLogMagnitude (T := T) := by
  unfold S1675OneColumnNormalization at h
  unfold qPilotMagnitude nativeGlobalQPilotNormalizedSignedLogVolume at *
  rw [h]
  ring

/-- Conditional actual global comparison from the normalization and the native
hull magnitude bound. -/
theorem s1675GlobalComparison_of_normalization
    (D : S1675GlobalReadoutNormalizationData (I := I) R n T) :
    qPilotThetaHullComparison (I := I) R n := by
  apply (qPilotThetaHullComparison_iff (I := I) R n).mpr
  rw [s1675QPilotMagnitude_eq_native (I := I) T D.one_column_eq]
  exact D.hull_bound

/-- Exact first missing field: the one-column/native global q normalization. -/
abbrev S1675FirstMissingNormalization : Prop :=
  S1675OneColumnNormalization (I := I) T

end LeanFormal.IUT.XiFPaper.S1675GlobalReadoutNormalizationActual

end
