import tmp.sheaf.xif.paper.S2560TensorHaarActual
import tmp.sheaf.n8.closure.SourceAllowedOutputActualAttempt
import tmp.sheaf.n8.closure.SourceAllowedActualDataReduction
import tmp.sheaf.n8.closure.C3Actual
import tmp.sheaf.n8.closure.SourceWitnessedOutput
import tmp.sheaf.n8.closure.C2Actual

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.P6Bridge
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.N8Closure.SourceAllowedOutputActualAttempt
open LeanFormal.IUT.N8Closure.SourceAllowedActualDataReduction
open LeanFormal.IUT.N8Closure.C2Actual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper.S2560TensorHaarActual

namespace LeanFormal.IUT.XiFPaper.S2561SourceAllowedMeasureIntegrationActual

universe ua uv upi umon ui uL
variable {l : PrimeGeFive} {X : N8NativeInput l}

/-- Actual zero procession of the theta-pilot carrier. -/
def S2561zeroThetaPilotCarrier : ThetaPilotCarrier l := ⟨0, Nat.succ_pos _⟩

/-- C1PlaceData from the exact old bridge binding. -/
noncomputable def S2561c1PlaceDataOfDonors (D : P6BridgeDonors X) :
    C1PlaceData ((actualBridge D).input) where
  v := (actualBridge D).binding.place.selected
  R := (actualBridge D).binding.place.selected_realization

/-- Conditional actual C4 data from an actual IndActionData. -/
noncomputable def S2561c4DataOfInd (D : P6BridgeDonors X)
    (ind : IndActionData
      ((actualBridge D).input.ThetaPilotPoint (S2561c1PlaceDataOfDonors D).v)
      (PaperLabel l)) :
    SourceWitnessedOutputData (actualBridge D).input (PaperLabel l) where
  place := S2561c1PlaceDataOfDonors D
  pilot := ⟨S2561zeroThetaPilotCarrier (l := l)⟩
  ind := ind

/-- Build the SourceAllowedActualData package from the P6 bridge donors,
C3 donors, and the exact IndActionData; the tensor measure is supplied by
S2560 and C6/T11/C2 are actual. -/
noncomputable def S2561SourceAllowedActualData
    (D : P6BridgeDonors X)
    (C3d : SourcePilotRegionDonors (actualBridge D).input)
    (ind : IndActionData
      ((actualBridge D).input.ThetaPilotPoint (S2561c1PlaceDataOfDonors D).v)
      (PaperLabel l)) :
    SourceAllowedActualData X := by
  let C3 : SourcePilotRegionData (actualBridge D).input :=
    sourcePilotRegionDataOfDonors (actualBridge D).input C3d
  let D4 : SourceWitnessedOutputData (actualBridge D).input (PaperLabel l) :=
    S2561c4DataOfInd D ind
  let md : S2560TensorMeasureDonor C3.tensorPlaces C3.tensorTuple :=
    S2560C3TensorMeasureDonor C3
  letI : MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple) :=
    inferInstance
  letI : BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple) :=
    inferInstance
  letI : Measure.IsAddHaarMeasure md.mu := md.addHaar
  exact
    { donors := D
      C2 := sourceLogKummerDataActual (actualBridge D).input (actualBridge D).binding
      C3 := C3
      D := D4
      T := t11OfC3 D C3
      measurableSpace := inferInstance
      borelSpace := inferInstance
      mu := md.mu
      addHaar := md.addHaar
      B := C6ActualIQData.actual C3.tensorPlaces C3.tensorTuple md.mu }

theorem S2561SourceAllowedOutput_nonempty
    (D : P6BridgeDonors X)
    (C3d : SourcePilotRegionDonors (actualBridge D).input)
    (ind : IndActionData
      ((actualBridge D).input.ThetaPilotPoint (S2561c1PlaceDataOfDonors D).v)
      (PaperLabel l)) :
    Nonempty (SourceAllowedOutput X) := by
  exact sourceAllowedOutput_nonempty_of_actualData
    ⟨S2561SourceAllowedActualData D C3d ind⟩

#check S2561SourceAllowedActualData
#check S2561SourceAllowedOutput_nonempty
#print axioms S2561SourceAllowedOutput_nonempty
end LeanFormal.IUT.XiFPaper.S2561SourceAllowedMeasureIntegrationActual
end