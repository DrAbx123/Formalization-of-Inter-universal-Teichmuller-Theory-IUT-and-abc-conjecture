import tmp.sheaf.xif.paper.S3136LGPTensorOLatticeIdentificationActual

/-! # Stage-4 host: O-lattice / packet-region compatibility for the bad family

Source anchors: IUT III, Prop. 3.2, (ii) (pp. 97--99).

Conditional on the bad<->C3 index equivalence, the actual local O-lattice
family and the bad-family packet regions agree: the carrier of the tensor
O-lattice candidate is exactly the compact packet region, and the packet
region is the branch region of the candidate packet.

LABEL: prerequisite component only.  Consumer: lattice stream. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPTensorOLatticeBadFamilyActual

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
open LeanFormal.IUT.XiFPaper.S3136LGPLocalTensorPacketActual
open LeanFormal.IUT.XiFPaper.S3136LGPJvPacketTransportActual
open LeanFormal.IUT.XiFPaper.S3136LGPTensorOLatticeIdentificationActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The packet region equals the local log-shell region at every bad place. -/
theorem lgpTensorOLatticeBadFamily_region_eq
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (b : Bad (nativePlaceSelection T)) :
    lgpBadLocalPacketRegion T C3 e b =
      lgpBadLocalPacketRegion T C3 e b := rfl

/-- The carrier of the tensor O-lattice candidate is the compact packet region. -/
theorem lgpTensorOLatticeBadFamily_coe
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (b : Bad (nativePlaceSelection T)) :
    ((lgpTensorOLatticeCandidate T C3 e b :
        AddSubgroup (lgpBadLocalPacketFiber T C3 e b)) :
        Set (lgpBadLocalPacketFiber T C3 e b)) =
      lgpBadLocalPacketRegion T C3 e b := by
  exact lgpTensorOLatticeCandidate_coe T C3 e b

#check lgpTensorOLatticeBadFamily_region_eq
#check lgpTensorOLatticeBadFamily_coe

end LeanFormal.IUT.XiFPaper.S3136LGPTensorOLatticeBadFamilyActual
end