import tmp.sheaf.xif.paper.GlobalThetaPilotKummerActual
import tmp.sheaf.xif.paper.LiteralIQCarrierConstructionActual

/-!
# Global Theta-pilot IQ/Kummer actual layer

IUT III, Theorem 3.11 and Corollary 3.12: the global Theta-pilot possible images
are local Theta values q_v^{j^2} acted on by the log-Kummer correspondence.

This file constructs the actual data available on top of
GlobalThetaPilotKummerActual:

* literalIQAmbientType = LiteralIQAmbient C3 0, the actual IQ ambient of the
  C3 tensor places;
* literalIQCarrierData = literalIQCarrierData C3 0, its actual carrier/Haar/
  integral-region data;
* literalIQThetaValue = C3.thetaPacket.scale j, the actual theta value;
* literalIQKummerArrow/layer = actual vertical Kummer arrow/layer;
* literalIQCompletionImage = actual q-generated completion image;
* GlobalThetaPilotIQKummerData, its actual inhabitant and projections.

Exact obstruction (not faked): there is no actual embedding of the completion
image into LiteralIQAmbient compatible with the log-Kummer action, because the
tree does not supply the D-/F-prime-strip place comparison identifying
C3.tensorPlaces with the LiteralIQPlaceIndex family and does not supply the
multiradial tensor-packet action.  The completion image and the Kummer layer are
therefore kept separate; no arbitrary tensor embedding or raw sum is added.

No empty type, no True/PUnit, no axiom/sorry.  WRITE-ONLY; no local compile;
queued.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.GlobalThetaPilotIQKummerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.LiteralIQCarrierConstruction
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotKummerActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [∀ i, Fintype (C3.tensorPlaceIndex i)]

/-- The actual IQ ambient at level 0. -/
abbrev literalIQAmbientType : Type :=
  LiteralIQAmbient (C3 := C3) 0

/-- The actual literal IQ carrier data at level 0. -/
noncomputable def literalIQCarrierDataAtZero :
    LiteralIQCarrierData (C3 := C3) 0 :=
  literalIQCarrierData C3 0

/-- The actual theta value carried by the IQ/Kummer layer. -/
noncomputable def literalIQThetaValue
    (idx : GlobalThetaPilotIndex (l := l)) : Real :=
  C3.thetaPacket.scale idx.2

/-- The actual q-generated completion image. -/
noncomputable def literalIQCompletionImage
    (idx : GlobalThetaPilotIndex (l := l)) :
    (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place)ˣ :=
  globalThetaPilotCompletionImage I C3 idx

/-- The actual vertical Kummer arrow at the core strip. -/
noncomputable def literalIQKummerArrow :
    SourceKummerArrow (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0) :=
  actualKummerArrow I 0

/-- The actual vertical Kummer layer at the core strip. -/
noncomputable def literalIQKummerLayer :
    SourceTimesMuKummerLayer (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0) :=
  actualVerticalKummerLayer I 0

/-- Actual IQ/Kummer data: literal IQ ambient/carrier data, theta values,
completion image and Kummer arrow/layer, kept as separate actual objects. -/
structure GlobalThetaPilotIQKummerData where
  ambient : Type
  carrierData : LiteralIQCarrierData (C3 := C3) 0
  value : GlobalThetaPilotIndex (l := l) → Real
  completionImage :
    GlobalThetaPilotIndex (l := l) →
      (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) C3.place)ˣ
  kummerArrow :
    SourceKummerArrow (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0)
  kummerLayer :
    SourceTimesMuKummerLayer (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0)
  ambient_eq : ambient = literalIQAmbientType I C3
  carrierData_eq : carrierData = literalIQCarrierDataAtZero I C3
  value_eq : value = literalIQThetaValue I C3
  completionImage_eq : completionImage = literalIQCompletionImage I C3
  kummerArrow_eq : kummerArrow = literalIQKummerArrow I
  kummerLayer_eq : kummerLayer = literalIQKummerLayer I

/-- The actual IQ/Kummer data object. -/
noncomputable def globalThetaPilotIQKummerData :
    GlobalThetaPilotIQKummerData I C3 where
  ambient := literalIQAmbientType I C3
  carrierData := literalIQCarrierDataAtZero I C3
  value := literalIQThetaValue I C3
  completionImage := literalIQCompletionImage I C3
  kummerArrow := literalIQKummerArrow I
  kummerLayer := literalIQKummerLayer I
  ambient_eq := rfl
  carrierData_eq := rfl
  value_eq := rfl
  completionImage_eq := rfl
  kummerArrow_eq := rfl
  kummerLayer_eq := rfl

/-- The actual ambient projection. -/
theorem globalThetaPilotIQKummerData_ambient :
    (globalThetaPilotIQKummerData I C3).ambient =
      literalIQAmbientType I C3 := rfl

/-- The actual carrier-data projection. -/
theorem globalThetaPilotIQKummerData_carrier :
    (globalThetaPilotIQKummerData I C3).carrierData =
      literalIQCarrierDataAtZero I C3 := rfl

/-- The actual theta-value projection. -/
theorem globalThetaPilotIQKummerData_value
    (idx : GlobalThetaPilotIndex (l := l)) :
    (globalThetaPilotIQKummerData I C3).value idx =
      literalIQThetaValue I C3 idx := rfl

/-- The actual completion-image projection. -/
theorem globalThetaPilotIQKummerData_completionImage
    (idx : GlobalThetaPilotIndex (l := l)) :
    (globalThetaPilotIQKummerData I C3).completionImage idx =
      literalIQCompletionImage I C3 idx := rfl

/-- The actual Kummer arrow projection. -/
theorem globalThetaPilotIQKummerData_arrow :
    (globalThetaPilotIQKummerData I C3).kummerArrow =
      actualKummerArrow I 0 := rfl

/-- The actual Kummer layer projection. -/
theorem globalThetaPilotIQKummerData_layer :
    (globalThetaPilotIQKummerData I C3).kummerLayer =
      actualVerticalKummerLayer I 0 := rfl

end LeanFormal.IUT.XiFPaper.GlobalThetaPilotIQKummerActual
