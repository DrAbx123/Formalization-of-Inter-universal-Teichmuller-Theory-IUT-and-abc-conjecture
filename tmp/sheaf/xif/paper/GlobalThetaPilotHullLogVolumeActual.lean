import tmp.sheaf.xif.paper.WeakIQComparisonDataActual

/-!
# Global Theta-pilot hull log-volume

The actual global Theta-pilot product hull is

  globalThetaPilotHull R n
    = {x : (v : V) -> I.ThetaPilotPoint v |
        forall v, x v in I.sourceHolomorphicHull v (R v) n}.

The per-place actual source volume is I.sourceSetVolume v.  This file constructs
the global Theta-pilot hull log-volume as the sum over the actual finite place
type V of the logarithms of those per-place source volumes, together with the
image-side analogue and the actual q-pilot signed scalar.

No C3 unit region is used as a hull, no carrier equivalence is constructed, and
no q-pilot/Theta comparison inequality is asserted.

No PUnit/True, arbitrary data, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.GlobalThetaPilotHullLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ThetaPilotObjectActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- The actual per-place Theta-pilot hull volume. -/
def thetaHullVolumeAt (v : V) : ENNReal :=
  I.sourceSetVolume v (I.sourceHolomorphicHull v (R v) n)

/-- The actual per-place Theta-pilot image volume. -/
def thetaImageVolumeAt (v : V) : ENNReal :=
  I.sourceSetVolume v (I.possibleThetaPilotImageSet v (R v) n)

/-- The actual global Theta-pilot hull log-volume: sum of per-place logs. -/
def globalThetaHullLogVolume : Real :=
  ∑ v : V, Real.log (thetaHullVolumeAt (I := I) R n v).toReal

/-- The actual global Theta-pilot image log-volume: sum of per-place logs. -/
def globalThetaImageLogVolume : Real :=
  ∑ v : V, Real.log (thetaImageVolumeAt (I := I) R n v).toReal

/-- The actual q-pilot signed log-volume scalar. -/
def globalQPilotLogVolume : Real :=
  I.qPilotSignedLogVolume

/-- The global hull log-volume is the per-place sum. -/
theorem globalThetaHullLogVolume_eq :
    globalThetaHullLogVolume (I := I) R n =
      ∑ v : V, Real.log
        (I.sourceSetVolume v (I.sourceHolomorphicHull v (R v) n)).toReal := rfl

/-- The global image log-volume is the per-place sum. -/
theorem globalThetaImageLogVolume_eq :
    globalThetaImageLogVolume (I := I) R n =
      ∑ v : V, Real.log
        (I.sourceSetVolume v (I.possibleThetaPilotImageSet v (R v) n)).toReal := rfl

/-- The q-pilot scalar is the actual source signed q-pilot log. -/
theorem globalQPilotLogVolume_eq :
    globalQPilotLogVolume (I := I) = I.qPilotSignedLogVolume := rfl

/-- Actual per-place image volume is at most actual per-place hull volume. -/
theorem thetaImageVolumeAt_le_hullVolumeAt (v : V) :
    thetaImageVolumeAt (I := I) R n v ≤
      thetaHullVolumeAt (I := I) R n v :=
  I.sourceSetVolume_mono v
    (I.possibleThetaPilotImage_subset_sourceHolomorphicHull v (R v) n)

/-- Weak comparison data: actual q-pilot scalar, global image and hull
log-volumes, and per-place volumes. -/
structure GlobalThetaPilotHullLogVolumeData where
  qPilotLogVolume : Real
  thetaImageLogVolume : Real
  thetaHullLogVolume : Real
  imageVolumeAt : V → ENNReal
  hullVolumeAt : V → ENNReal
  imageVolumeAt_eq : imageVolumeAt = thetaImageVolumeAt (I := I) R n
  hullVolumeAt_eq : hullVolumeAt = thetaHullVolumeAt (I := I) R n
  thetaImageLogVolume_eq : thetaImageLogVolume =
    globalThetaImageLogVolume (I := I) R n
  thetaHullLogVolume_eq : thetaHullLogVolume =
    globalThetaHullLogVolume (I := I) R n
  qPilotLogVolume_eq : qPilotLogVolume = I.qPilotSignedLogVolume

/-- The actual global Theta-pilot hull log-volume data. -/
noncomputable def globalThetaPilotHullLogVolumeData :
    GlobalThetaPilotHullLogVolumeData (I := I) R n where
  qPilotLogVolume := globalQPilotLogVolume (I := I)
  thetaImageLogVolume := globalThetaImageLogVolume (I := I) R n
  thetaHullLogVolume := globalThetaHullLogVolume (I := I) R n
  imageVolumeAt := thetaImageVolumeAt (I := I) R n
  hullVolumeAt := thetaHullVolumeAt (I := I) R n
  imageVolumeAt_eq := rfl
  hullVolumeAt_eq := rfl
  thetaImageLogVolume_eq := rfl
  thetaHullLogVolume_eq := rfl
  qPilotLogVolume_eq := rfl

/-- The constructed hull log-volume is the actual per-place sum. -/
@[simp] theorem globalThetaPilotHullLogVolumeData_hull :
    (globalThetaPilotHullLogVolumeData (I := I) R n).thetaHullLogVolume =
      ∑ v : V, Real.log
        (I.sourceSetVolume v (I.sourceHolomorphicHull v (R v) n)).toReal := rfl

/-- The constructed q-pilot scalar is the actual signed q-pilot log. -/
@[simp] theorem globalThetaPilotHullLogVolumeData_qPilot :
    (globalThetaPilotHullLogVolumeData (I := I) R n).qPilotLogVolume =
      I.qPilotSignedLogVolume := rfl

end LeanFormal.IUT.XiFPaper.GlobalThetaPilotHullLogVolumeActual

end