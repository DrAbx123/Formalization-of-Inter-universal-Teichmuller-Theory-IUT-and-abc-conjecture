import tmp.sheaf.n8.closure.SourceThetaToIQ
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierHaarData

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8C6ActualIQ
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2605C6SourceBridgeActualAdapted

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable {Label : Type uL} [Group Label]
variable (D : SourceWitnessedOutputData (l := l) (V := V) I Label)

structure ThetaPilotToC6Embedding where
  toC6 : I.ThetaPilotPoint D.place.v -> IQCarrier C3
  inv : IQCarrier C3 -> I.ThetaPilotPoint D.place.v
  inv_toC6 : forall x : I.ThetaPilotPoint D.place.v, inv (toC6 x) = x

noncomputable def C6SourceUnitRegion
    (E : ThetaPilotToC6Embedding (I := I) (C3 := C3) (D := D))
    (Ds : I.SourceUnitRegionHaarData D.place.v D.place.R D.pilot.n) :
    Set (IQCarrier C3) :=
  E.toC6 '' Ds.unitRegion

noncomputable def C6SourceScaleShift
    (E : ThetaPilotToC6Embedding (I := I) (C3 := C3) (D := D))
    (Ds : I.SourceUnitRegionHaarData D.place.v D.place.R D.pilot.n) :
    IQCarrier C3 -> IQCarrier C3 :=
  fun y => E.toC6 (Ds.scaling * E.inv y)

theorem C6SourceScaleShift_apply
    (E : ThetaPilotToC6Embedding (I := I) (C3 := C3) (D := D))
    (Ds : I.SourceUnitRegionHaarData D.place.v D.place.R D.pilot.n)
    (x : I.ThetaPilotPoint D.place.v) :
    C6SourceScaleShift I C3 D E Ds (E.toC6 x) =
      E.toC6 (Ds.scaling * x) := by
  simp [C6SourceScaleShift, E.inv_toC6]

#print axioms C6SourceScaleShift_apply

end LeanFormal.IUT.XiFPaper.S2605C6SourceBridgeActualAdapted
end
