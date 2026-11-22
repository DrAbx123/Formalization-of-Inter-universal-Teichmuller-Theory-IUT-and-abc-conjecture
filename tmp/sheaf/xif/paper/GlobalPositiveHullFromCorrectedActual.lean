import tmp.sheaf.xif.paper.SourceHullVolumeSignCorrectedActual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Global positive Theta-hull log-volume from the corrected source volume

This file uses the corrected positive source hull log-volume

  SourceHullVolumeSignCorrectedActual.positiveHullLogVolume

(the supremum of positive point log-volumes, not the old
ENNReal.ofReal of a negative log-degree and not sourceHullVolume).

It constructs actual global scalar data:

* positiveHullLogVolumeAt v n : Real, the corrected positive hull log-volume at
  a global place v;
* globalPositiveThetaHullLogVolume : Real, the sum over the actual global place
  type V;
* vBadPositiveThetaHullLogVolume, the sum over the native bad family for an
  explicitly supplied bad-to-global place map;
* the direct comparison scalar with the native q-pilot normalized magnitude,
  as a real difference.

No inequality is asserted or judged. No old sourceHullVolume is used. No
True/PUnit, empty type, axiom, or sorry is used.
-/

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.GlobalPositiveHullFromCorrectedActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.OriginalInput.SourceHullVolumeSignCorrectedActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : ∀ v : V, I.SourceImageRealization v)
variable (n : ThetaPilotCarrier l)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The corrected positive Theta-hull log-volume at one global place, as an
actual real scalar (ENNReal toReal of the corrected positive hull volume). -/
noncomputable def positiveHullLogVolumeAt (v : V) : Real :=
  (positiveHullLogVolume (I := I) v (R v) n).toReal

/-- The per-place scalar is exactly the toReal of the corrected positive hull
log-volume. -/
theorem positiveHullLogVolumeAt_eq (v : V) :
    positiveHullLogVolumeAt (I := I) R n v =
      (positiveHullLogVolume (I := I) v (R v) n).toReal :=
  rfl

/-- The actual global positive Theta-hull log-volume: sum over the global place
type V of the corrected positive per-place hull values. -/
noncomputable def globalPositiveThetaHullLogVolume : Real :=
  ∑ v : V, positiveHullLogVolumeAt (I := I) R n v

/-- The global scalar is the per-place sum. -/
theorem globalPositiveThetaHullLogVolume_eq :
    globalPositiveThetaHullLogVolume (I := I) R n =
      ∑ v : V, positiveHullLogVolumeAt (I := I) R n v :=
  rfl

/-- The actual V_bad-indexed positive Theta-hull log-volume, for an explicitly
supplied actual bad-to-global place map. -/
noncomputable def vBadPositiveThetaHullLogVolume
    (badToV : Bad (nativePlaceSelection T) → V) : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    (positiveHullLogVolume (I := I) (badToV b) (R (badToV b)) n).toReal

/-- The V_bad sum is the corresponding per-bad-place sum. -/
theorem vBadPositiveThetaHullLogVolume_eq
    (badToV : Bad (nativePlaceSelection T) → V) :
    vBadPositiveThetaHullLogVolume (I := I) R n T badToV =
      ∑ b : Bad (nativePlaceSelection T),
        (positiveHullLogVolume (I := I) (badToV b) (R (badToV b)) n).toReal :=
  rfl

/-- The actual native q-pilot normalized magnitude scalar used for comparison. -/
noncomputable def nativeQPilotComparisonMagnitude : Real :=
  nativeGlobalQPilotNormalizedLogMagnitude T

/-- The actual native q-pilot normalized signed scalar used for comparison. -/
noncomputable def nativeQPilotComparisonSigned : Real :=
  nativeGlobalQPilotNormalizedSignedLogVolume T

/-- The direct scalar difference: global positive Theta-hull log-volume minus
the native q-pilot normalized magnitude. This is actual comparison data, not an
asserted inequality. -/
noncomputable def positiveHullMinusNativeQPilotMagnitude : Real :=
  globalPositiveThetaHullLogVolume (I := I) R n -
    nativeQPilotComparisonMagnitude T

/-- The signed direct scalar difference: the negative global positive Theta-hull
log-volume minus the native signed q-pilot scalar. -/
noncomputable def negativePositiveHullMinusNativeQPilotSigned : Real :=
  -globalPositiveThetaHullLogVolume (I := I) R n -
    nativeQPilotComparisonSigned T

/-- The comparison magnitude is the actual native global q-pilot magnitude. -/
theorem nativeQPilotComparisonMagnitude_eq :
    nativeQPilotComparisonMagnitude T =
      nativeGlobalQPilotNormalizedLogMagnitude T :=
  rfl

/-- The comparison signed scalar is the actual native global q-pilot signed
log-volume. -/
theorem nativeQPilotComparisonSigned_eq :
    nativeQPilotComparisonSigned T =
      nativeGlobalQPilotNormalizedSignedLogVolume T :=
  rfl

end LeanFormal.IUT.XiFPaper.GlobalPositiveHullFromCorrectedActual

end
