import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHull
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import tmp.sheaf.xif.paper.BaseQLogVolumeActual
import tmp.sheaf.xif.paper.SourceHullVolumeSignCorrectedActual
import tmp.sheaf.n8.closure.NativeBadLiftActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction

/-!
# Weak Theta-hull/log data with the corrected positive hull log-volume

The old `sourceHullVolume` is a supremum of `sourcePointVolume` values, where
`sourcePointVolume = ENNReal.ofReal (sourceLocalLogDegree)`.  For theta-pilot
points the log-degree is negative, so the ENNReal value is truncated to zero.
That object is not valid for the paper xi-f positive log-volume.

This file rewrites the hull log-volume using the actual corrected positive
hull log-volume of `SourceHullVolumeSignCorrectedActual`:

* `positiveSetLogVolume` and `positiveHullLogVolume`;
* the actual possible image set and source holomorphic hull;
* the actual image/hull positive volumes and hull log;
* the actual pointwise q-pilot log magnitude.

The comparison field `hullLog ≤ qPilotLog` is a proposition, not asserted.
No truncation at zero is used for the hull log.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper
namespace WeakThetaHullDataActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.OriginalInput.SourceHullVolumeSignCorrectedActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The actual possible Theta-pilot image set. -/
abbrev weakThetaImageSet
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    Set (I.ThetaPilotPoint v) :=
  I.possibleThetaPilotImageSet v R n

/-- The actual holomorphic hull of the possible image set. -/
abbrev weakThetaHull
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    Set (I.ThetaPilotPoint v) :=
  I.sourceHolomorphicHull v R n

/-- The actual image set is contained in the actual hull. -/
theorem weakThetaImageSet_subset_hull
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    weakThetaImageSet (I := I) v R n ⊆ weakThetaHull (I := I) v R n :=
  I.possibleThetaPilotImage_subset_sourceHolomorphicHull v R n

/-- The corrected positive image-union log-volume, not the old ENNReal
truncation. -/
noncomputable abbrev weakThetaImageVolume
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    ENNReal :=
  positiveSetLogVolume (I := I) v (weakThetaImageSet (I := I) v R n)

/-- The corrected positive hull log-volume. -/
noncomputable abbrev weakThetaHullVolume
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    ENNReal :=
  positiveHullLogVolume (I := I) v R n

/-- The actual corrected real-valued hull log. -/
noncomputable abbrev weakThetaHullLog
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    Real :=
  (positiveHullLogVolume (I := I) v R n).toReal

/-- The actual corrected real-valued image log. -/
noncomputable abbrev weakThetaImageLog
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    Real :=
  (positiveSetLogVolume (I := I) v (weakThetaImageSet (I := I) v R n)).toReal

/-- The weak data supporting the Theta-hull/q-pilot comparison, with the
corrected positive hull log. -/
structure WeakThetaHullLogData
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  imageSet : Set (I.ThetaPilotPoint v)
  imageSet_eq : imageSet = weakThetaImageSet (I := I) v R n
  hull : Set (I.ThetaPilotPoint v)
  hull_eq : hull = weakThetaHull (I := I) v R n
  imageSet_subset_hull : imageSet ⊆ hull
  imageVolume : ENNReal
  imageVolume_eq : imageVolume = weakThetaImageVolume (I := I) v R n
  hullVolume : ENNReal
  hullVolume_eq : hullVolume = weakThetaHullVolume (I := I) v R n
  hullLog : Real
  hullLog_eq : hullLog = weakThetaHullLog (I := I) v R n
  qPilotLog : Real
  qPilotLog_eq : qPilotLog = baseQLogMagnitude T b
  thetaHullLeQPilot : Prop
  thetaHullLeQPilot_eq : thetaHullLeQPilot = (hullLog ≤ qPilotLog)

/-- The actual weak hull/log data with the corrected positive hull log. -/
noncomputable def weakThetaHullLogData
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    WeakThetaHullLogData (l := l) (V := V) (I := I) v R n T b where
  imageSet := weakThetaImageSet (I := I) v R n
  imageSet_eq := rfl
  hull := weakThetaHull (I := I) v R n
  hull_eq := rfl
  imageSet_subset_hull := weakThetaImageSet_subset_hull (I := I) v R n
  imageVolume := weakThetaImageVolume (I := I) v R n
  imageVolume_eq := rfl
  hullVolume := weakThetaHullVolume (I := I) v R n
  hullVolume_eq := rfl
  hullLog := weakThetaHullLog (I := I) v R n
  hullLog_eq := rfl
  qPilotLog := baseQLogMagnitude T b
  qPilotLog_eq := rfl
  thetaHullLeQPilot := weakThetaHullLog (I := I) v R n ≤
    baseQLogMagnitude T b
  thetaHullLeQPilot_eq := rfl

/-- The corrected hull log is the positive hull log, not the old truncated
`sourceHullVolume`. -/
theorem weakThetaHullLog_eq_positiveHullLog
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    weakThetaHullLog (I := I) v R n =
      (positiveHullLogVolume (I := I) v R n).toReal := rfl

end WeakThetaHullDataActual
end LeanFormal.IUT.XiFPaper
end
