import tmp.sheaf.xif.paper.S3136LGPLocalTensorPacketActual

/-! # Stage-4 host: bad-family local packet (all bad places at once)

Source anchors: IUT III, Prop. 3.2, (ii) (pp. 97--99); Prop. 3.4, (ii)
(pp. 102--103).

Conditional on the named bad<->C3 index equivalence, this file packages the
candidate local LGP tensor packets as one actual family over all bad places:
* lgpBadFamilyPacket e: the family of actual candidate packets (previous batch);
* family compactness / IQ / Haar / region compatibility projection theorems;
* lgpBadFamily_place_agree: under the qpilot bad-to-all-place injection, every
  bad-place fiber equals the all-place tensor fiber;
* lgpBadFamilyDimension_pos: the family block has positive actual dimension;
* LGPBadFamilyMissing/Gap: exact missing data (index equivalence, injection,
  Galois action, label components, log-link compatibility; refs above).

LABEL: prerequisite component only.  Consumer: lattice stream,
IUT-III.theta-xmu-LGP-full-poly-isomorphism. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPBadFamilyPacketActual

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
open LeanFormal.IUT.XiFPaper.S3133QPilotOneColumnRegionCarrierActual
open LeanFormal.IUT.XiFPaper.S3136LGPLocalTensorPacketActual
open LeanFormal.IUT.LocalFieldLogarithm

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual family of candidate local LGP tensor packets over the bad places. -/
noncomputable def lgpBadFamilyPacket
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex) :
    ∀ b : Bad (nativePlaceSelection T),
      LGPBadLocalPacketCandidate T C3 e b :=
  fun b => lgpBadLocalPacketCandidate T C3 e b

/-- Every family member has the compact actual local region. -/
theorem lgpBadFamilyPacket_region_compact
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (b : Bad (nativePlaceSelection T)) :
    IsCompact (lgpBadFamilyPacket T C3 e b).region :=
  (lgpBadFamilyPacket T C3 e b).region_compact

/-- Every family member carries the actual IQ Q-span. -/
theorem lgpBadFamilyPacket_iqCarrier_eq
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (b : Bad (nativePlaceSelection T)) :
    (lgpBadFamilyPacket T C3 e b).iqCarrier = actualC3LogShellTensorIQ C3 :=
  (lgpBadFamilyPacket T C3 e b).iqCarrier_eq

/-- Every family member carries the actual additive Haar measure. -/
theorem lgpBadFamilyPacket_haar_eq
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (b : Bad (nativePlaceSelection T)) :
    (lgpBadFamilyPacket T C3 e b).haar = actualC3LogShellTensorHaar C3 :=
  (lgpBadFamilyPacket T C3 e b).haar_eq

/-- Under the qpilot bad-to-all-place injection, every bad-place packet fiber
agrees with the corresponding all-place tensor fiber. -/
theorem lgpBadFamily_place_agree
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (indexEquiv : V ≃ C3.tensorIndex)
    (h : S3133BadToAllPlaceIndexInjection T C3 e indexEquiv)
    (b : Bad (nativePlaceSelection T)) :
    lgpBadLocalPacketFiber T C3 e b =
      C3LogShellFiber C3 (indexEquiv (h.badToV b)) :=
  lgpBadLocalPacket_place_agree T C3 e indexEquiv h b

/-- The family tensor block has positive actual dimension. -/
theorem lgpBadFamilyDimension_pos : 0 < qPilotOneColumnDimension C3 :=
  qPilotOneColumnDimension_pos C3

/-- Exact missing data for the bad-family packet (IUT III, Prop. 3.2, (ii),
pp. 97--99; Prop. 3.4, (ii), pp. 102--103): index equivalence, bad-to-all-place
injection, Galois action, label components, log-link compatibility. -/
structure LGPBadFamilyMissing where
  badTensorIndexEquivalence : Prop
  badToAllPlaceIndexInjection : Prop
  galoisActionOnFamily : Prop
  labelComponents : Prop
  logLinkCompatibility : Prop

/-- The exact bad-family gap. -/
def LGPBadFamilyGap : Prop := Nonempty LGPBadFamilyMissing

#check lgpBadFamilyPacket
#check lgpBadFamilyPacket_region_compact
#check lgpBadFamily_place_agree
#check lgpBadFamilyDimension_pos
#check LGPBadFamilyGap

end LeanFormal.IUT.XiFPaper.S3136LGPBadFamilyPacketActual
end