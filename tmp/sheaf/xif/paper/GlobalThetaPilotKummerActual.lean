import tmp.sheaf.xif.paper.GlobalThetaPilotLogVolumeActual
import tmp.sheaf.xif.paper.ThetaPilotQImagePartialActual
import tmp.sheaf.xif.paper.LogKummerCorrespondenceFromSource
import tmp.sheaf.xif.paper.LiteralIQCarrierConstructionActual

/-!
# Global Theta-pilot Kummer actual data

IUT III, Theorem 3.11 and Corollary 3.12: the global Theta-pilot possible images
are the collection over V_bad of the local Theta values q_v^{j^2}, acted on by
the log-Kummer correspondence.  This file constructs the actual data available
from the source:

* the global Theta-pilot index (ThetaPilotCarrier x SignedLabel);
* the actual theta value C3.thetaPacket.scale j at each index (no raw sum);
* the actual q-generated completion image C3.qUnit^(gauss exponent);
* the actual vertical Kummer arrow/layer from LogKummerCorrespondenceFromSource;
* the actual Kummer isomorphisms at every place;
* the actual finite completion-image set and its compactness.

The remaining global multiradial representation is NOT fabricated.  Exact
obstruction: there is no actual map from the completion image to the literal IQ
ambient (LiteralIQAmbient of the C3 tensor places) compatible with the
log-Kummer action, and no global possible-image union over all V_bad; the tree
provides the local q-generated image and the Kummer arrow separately.  Those
identifications require the D-/F-prime-strip place comparison and the
multiradial representation, which are not supplied here.

No raw sum, no empty type, no True/PUnit, no axiom/sorry.  WRITE-ONLY; no local
compile; queued.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.GlobalThetaPilotKummerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.ThetaPilotQImagePartialActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The global Theta-pilot image index: procession label times signed theta
label. -/
abbrev GlobalThetaPilotIndex : Type :=
  ThetaPilotImageIndex (l := l)

/-- The actual local theta value at an index: the source theta packet scale. -/
noncomputable def globalThetaPilotValue
    (idx : GlobalThetaPilotIndex (l := l)) : Real :=
  C3.thetaPacket.scale idx.2

/-- The actual q-generated completion image at an index. -/
noncomputable def globalThetaPilotCompletionImage
    (idx : GlobalThetaPilotIndex (l := l)) :
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place)ˣ :=
  thetaPilotCompletionImageMap (C3 := C3) idx

/-- The actual theta value is positive. -/
theorem globalThetaPilotValue_pos
    (idx : GlobalThetaPilotIndex (l := l)) :
    0 < globalThetaPilotValue I C3 idx :=
  C3.thetaPacket.scale_pos idx.2

/-- The actual theta value is the realized theta value. -/
theorem globalThetaPilotValue_eq_scale
    (idx : GlobalThetaPilotIndex (l := l)) :
    globalThetaPilotValue I C3 idx = C3.thetaPacket.scale idx.2 := rfl

/-- The actual completion image is the q-generated theta image. -/
theorem globalThetaPilotCompletionImage_eq
    (idx : GlobalThetaPilotIndex (l := l)) :
    globalThetaPilotCompletionImage I C3 idx =
      thetaPilotCompletionImageMap (C3 := C3) idx := rfl

/-- The actual global possible completion-image set. -/
def globalThetaPilotCompletionImageSet :
    Set ((CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place)ˣ) :=
  Set.range (globalThetaPilotCompletionImage I C3)

/-- The completion-image set is finite. -/
theorem globalThetaPilotCompletionImageSet_finite :
    (globalThetaPilotCompletionImageSet I C3).Finite :=
  Set.finite_range _

/-- The completion-image set is compact in the actual completion. -/
theorem globalThetaPilotCompletionImageSet_compact :
    IsCompact (globalThetaPilotCompletionImageSet I C3) :=
  thetaPilotCompletionImageSet_compact (C3 := C3)

/-- The actual vertical Kummer arrow at the core strip. -/
noncomputable def globalThetaPilotKummerArrow :
    SourceKummerArrow (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0) :=
  actualKummerArrow I 0

/-- The actual vertical Kummer layer at the core strip. -/
noncomputable def globalThetaPilotKummerLayer :
    SourceTimesMuKummerLayer (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0) :=
  actualVerticalKummerLayer I 0

/-- The actual x-mu Kummer isomorphism at each place. -/
noncomputable def globalThetaPilotKummerIsomorphism (v : V) :
    TimesMuKummer.Isomorphism
      ((globalThetaPilotKummerLayer I).sourceAction v)
      ((globalThetaPilotKummerLayer I).targetAction v) :=
  (globalThetaPilotKummerLayer I).kummer v

/-- The actual global Theta-pilot Kummer data assembled from the source. -/
structure GlobalThetaPilotKummerActualData where
  value : GlobalThetaPilotIndex (l := l) → Real
  completionImage :
    GlobalThetaPilotIndex (l := l) →
      (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place)ˣ
  possibleImageSet :
    Set ((CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place)ˣ)
  kummerArrow :
    SourceKummerArrow (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0)
  kummerLayer :
    SourceTimesMuKummerLayer (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0)
  value_eq : value = globalThetaPilotValue I C3
  completionImage_eq :
    completionImage = globalThetaPilotCompletionImage I C3
  possibleImageSet_eq :
    possibleImageSet = globalThetaPilotCompletionImageSet I C3
  kummerArrow_eq : kummerArrow = globalThetaPilotKummerArrow I
  kummerLayer_eq : kummerLayer = globalThetaPilotKummerLayer I

/-- The actual global Theta-pilot Kummer data. -/
noncomputable def globalThetaPilotKummerActualData :
    GlobalThetaPilotKummerActualData I C3 where
  value := globalThetaPilotValue I C3
  completionImage := globalThetaPilotCompletionImage I C3
  possibleImageSet := globalThetaPilotCompletionImageSet I C3
  kummerArrow := globalThetaPilotKummerArrow I
  kummerLayer := globalThetaPilotKummerLayer I
  value_eq := rfl
  completionImage_eq := rfl
  possibleImageSet_eq := rfl
  kummerArrow_eq := rfl
  kummerLayer_eq := rfl

/-- The actual value projection. -/
theorem globalThetaPilotKummerActualData_value
    (idx : GlobalThetaPilotIndex (l := l)) :
    (globalThetaPilotKummerActualData I C3).value idx =
      globalThetaPilotValue I C3 idx := rfl

/-- The actual completion-image projection. -/
theorem globalThetaPilotKummerActualData_completionImage
    (idx : GlobalThetaPilotIndex (l := l)) :
    (globalThetaPilotKummerActualData I C3).completionImage idx =
      globalThetaPilotCompletionImage I C3 idx := rfl

/-- The actual possible-image set is finite. -/
theorem globalThetaPilotKummerActualData_possibleImageSet_finite :
    (globalThetaPilotKummerActualData I C3).possibleImageSet.Finite :=
  globalThetaPilotCompletionImageSet_finite I C3

/-- The actual possible-image set is compact. -/
theorem globalThetaPilotKummerActualData_possibleImageSet_compact :
    IsCompact (globalThetaPilotKummerActualData I C3).possibleImageSet :=
  globalThetaPilotCompletionImageSet_compact I C3

/-- The actual Kummer arrow projection. -/
theorem globalThetaPilotKummerActualData_arrow :
    (globalThetaPilotKummerActualData I C3).kummerArrow =
      actualKummerArrow I 0 := rfl

/-- The actual Kummer layer projection. -/
theorem globalThetaPilotKummerActualData_layer :
    (globalThetaPilotKummerActualData I C3).kummerLayer =
      actualVerticalKummerLayer I 0 := rfl

end LeanFormal.IUT.XiFPaper.GlobalThetaPilotKummerActual
