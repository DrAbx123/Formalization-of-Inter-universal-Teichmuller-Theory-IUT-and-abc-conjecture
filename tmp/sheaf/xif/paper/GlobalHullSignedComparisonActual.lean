import tmp.sheaf.xif.paper.GlobalThetaPilotHullLogVolumeActual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual

-- Global hull signed comparison: actual objects and exact condition
--
-- signedThetaHull := -globalThetaHullLogVolume (sum of actual per-place
-- source-hull volume logs). The paper signed direction
-- nativeGlobalQPilotNormalizedSignedLogVolume <= signedThetaHull is equivalent
-- to the magnitude comparison globalThetaHullLogVolume <= native normalized
-- q-pilot magnitude. The latter is not proved; it is recorded as the exact
-- condition/obstruction, not fabricated. WRITE-ONLY: no local lake/lean.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.GlobalHullSignedComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotHullLogVolumeActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l)
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

-- The signed Theta-hull scalar: negative of the actual global hull log-volume.
noncomputable def signedThetaHullLogVolume : Real :=
  -globalThetaHullLogVolume (I := I) R n

-- The exact paper-direction signed comparison requirement.
def GlobalHullSignedComparisonRequired (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))] : Prop :=
  nativeGlobalQPilotNormalizedSignedLogVolume (T := T) ≤
    signedThetaHullLogVolume (I := I) R n

-- Its exact magnitude form: global hull log-volume <= native q-pilot magnitude.
def GlobalHullMagnitudeBoundRequired (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))] : Prop :=
  globalThetaHullLogVolume (I := I) R n ≤
    nativeGlobalQPilotNormalizedLogMagnitude (T := T)

-- The signed comparison is exactly the magnitude comparison.
theorem globalHullSignedComparison_iff_magnitude :
    GlobalHullSignedComparisonRequired (I := I) R n T ↔
      GlobalHullMagnitudeBoundRequired (I := I) R n T := by
  unfold GlobalHullSignedComparisonRequired signedThetaHullLogVolume
  unfold GlobalHullMagnitudeBoundRequired nativeGlobalQPilotNormalizedSignedLogVolume
  constructor <;> intro h <;> linarith

-- Conditional actual proof of the signed comparison from the exact magnitude
-- bound.
theorem globalHullSignedComparison_of_magnitudeBound
    (h : GlobalHullMagnitudeBoundRequired (I := I) R n T) :
    GlobalHullSignedComparisonRequired (I := I) R n T :=
  (globalHullSignedComparison_iff_magnitude (I := I) R n T).mpr h

-- Exact obstruction: the magnitude bound is the missing comparison.
def GlobalHullMagnitudeBoundObstruction (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))] : Prop :=
  GlobalHullMagnitudeBoundRequired (I := I) R n T

#check signedThetaHullLogVolume
#check GlobalHullSignedComparisonRequired
#check GlobalHullMagnitudeBoundRequired
#check globalHullSignedComparison_iff_magnitude
#check globalHullSignedComparison_of_magnitudeBound
#check GlobalHullMagnitudeBoundObstruction

end LeanFormal.IUT.XiFPaper.GlobalHullSignedComparisonActual

end