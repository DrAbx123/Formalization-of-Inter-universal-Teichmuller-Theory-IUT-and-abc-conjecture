import tmp.sheaf.xif.paper.S3136LGPBadFamilyPacketActual

/-! # Stage-4 host: bad-family / all-place packet transports

Source anchors: IUT III, Prop. 3.2, (ii) (pp. 97--99); see qpilot
S3133BadToAllPlaceIndexInjectionActual for the injection data.

Conditional on the bad<->C3 index equivalence and the qpilot injection, this
file records the transports between the bad-family packet and the all-place
tensor data: the tensorPlace agreement for the identified indices, and the
fiber-level agreement for every bad place.

LABEL: prerequisite component only.  Consumer: lattice stream,
IUT-III.theta-xmu-LGP-full-poly-isomorphism. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPBadToAllPlaceTransportsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.S3133S3131PlaceIndexComparisonActual
open LeanFormal.IUT.XiFPaper.S3133BadToAllPlaceIndexInjectionActual
open LeanFormal.IUT.XiFPaper.S3136LGPLocalTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3136LGPBadFamilyPacketActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- TensorPlace agreement for the identified indices (qpilot injection). -/
theorem lgpBadFamilyIndex_agree
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (indexEquiv : V ≃ C3.tensorIndex)
    (h : S3133BadToAllPlaceIndexInjection T C3 e indexEquiv)
    (b : Bad (nativePlaceSelection T)) :
    C3.tensorPlaces (e b) (C3.tensorTuple (e b)) =
      C3.tensorPlaces (indexEquiv (h.badToV b))
        (C3.tensorTuple (indexEquiv (h.badToV b))) :=
  S3133BadToAllPlaceIndexInjection_tensorPlaces_agree T C3 e indexEquiv h b

/-- Fiber-level agreement for every bad place. -/
theorem lgpBadFamilyFiber_agree
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (indexEquiv : V ≃ C3.tensorIndex)
    (h : S3133BadToAllPlaceIndexInjection T C3 e indexEquiv)
    (b : Bad (nativePlaceSelection T)) :
    lgpBadLocalPacketFiber T C3 e b =
      C3LogShellFiber C3 (indexEquiv (h.badToV b)) :=
  lgpBadFamily_place_agree T C3 e indexEquiv h b

#check lgpBadFamilyIndex_agree
#check lgpBadFamilyFiber_agree

end LeanFormal.IUT.XiFPaper.S3136LGPBadToAllPlaceTransportsActual
end