import tmp.sheaf.xif.paper.S3133BadToAllPlaceIndexInjectionActual
import tmp.sheaf.xif.paper.S3133QPilotOneColumnRegionCarrierActual

/-! # Stage-4 host: V_bad-indexed local LGP tensor packet candidate

Source anchors: IUT III, Prop. 3.2, (ii) (pp. 97--99): the integral structure
I(alpha D_vQ) is built from tensor products/direct sums of local log-shells
I(D_v), and IQ(-) is its Q-span; IUT III, Prop. 3.4, (ii) (pp. 102--103): the
local LGP-monoids act on the label components inside the tensor packets
IQ(S^pm_{j+1,j}; F_v).

This file constructs the CANDIDATE V_bad-indexed local LGP tensor packet from the
existing actual C3 tensor packet/log-shell data, CONDITIONALLY on the named
missing bad<->C3 index comparison:
* lgpBadTensorIndex e b := e b for e : Bad ~= C3.tensorIndex;
* lgpBadLocalPacketFiber e b := the actual C3 log-shell fiber at index e b;
* lgpBadLocalPacketRegion e b := the actual local log-shell I(D_v) inside it,
  with transferred compactness (lgpBadLocalPacketRegion_compact);
* structure LGPBadLocalPacketCandidate e b: region + compactness + actual IQ
  Q-span + actual additive Haar + Haar measure property;
* actual inhabitant lgpBadLocalPacketCandidate (from the actual C3 packet);
* lgpBadLocalPacket_place_agree: under the injection data (e, indexEquiv,
  injection), the packet fiber at b agrees with the all-place tensor fiber
  (qpilot's S3133BadToAllPlaceIndexInjection);
* dimension: lgpLocalPacketDimension_pos transfers the actual C3 dimension
  positivity (qPilotOneColumnDimension_pos);
* LGPLocalPacketIdentificationMissing/Gap: exact missing fields to the paper
  IQ(A,alpha Fv) at V_bad (index equivalence, all-place injection, Galois
  action, label components, log-link compatibility; refs above + II Cor 4.8).

LABEL: prerequisite component only, NOT the paper's local tensor packet.
Consumer: lattice stream, IUT-III.theta-xmu-LGP-full-poly-isomorphism (R-A/R-C
interface). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPLocalTensorPacketActual

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
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldPadicTensor
open MeasureTheory

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance lgpTensorBlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance lgpTensorBlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

local instance lgpTensorBlockProperSpace :
    ProperSpace (C3LogShellTensorBlock C3) := inferInstance

local instance lgpTensorBlockLocallyCompactSpace :
    LocallyCompactSpace (C3LogShellTensorBlock C3) := inferInstance

/-- The bad-place index transported along the missing bad<->C3 index
equivalence. -/
def lgpBadTensorIndex (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (b : Bad (nativePlaceSelection T)) : C3.tensorIndex := e b

/-- The candidate local LGP packet fiber at a bad place: the actual C3 log-shell
fiber at the identified tensor index. -/
abbrev lgpBadLocalPacketFiber
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (b : Bad (nativePlaceSelection T)) : Type :=
  C3LogShellFiber C3 (lgpBadTensorIndex T C3 e b)

/-- The actual local log-shell region I(D_v) inside the candidate fiber. -/
noncomputable def lgpBadLocalPacketRegion
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (b : Bad (nativePlaceSelection T)) :
    Set (lgpBadLocalPacketFiber T C3 e b) :=
  actualC3LogShell C3 (lgpBadTensorIndex T C3 e b)

/-- The candidate local region is compact: transferred from the actual
compactness of the local log-shell I(D_v). -/
theorem lgpBadLocalPacketRegion_compact
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (b : Bad (nativePlaceSelection T)) :
    IsCompact (lgpBadLocalPacketRegion T C3 e b) := by
  unfold lgpBadLocalPacketRegion
  rw [actualC3LogShell_eq_integralLogShell]
  exact isCompact_integralLogShell
    (K := CommonPrimeCompletion (c3LogShellPlace C3 (lgpBadTensorIndex T C3 e b)))
    (p := C3.p)

/-- The candidate local LGP tensor packet at a bad place: region, compactness,
actual IQ Q-span, actual additive Haar measure and its Haar property. -/
structure LGPBadLocalPacketCandidate
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (b : Bad (nativePlaceSelection T)) where
  region : Set (lgpBadLocalPacketFiber T C3 e b)
  region_eq : region = lgpBadLocalPacketRegion T C3 e b
  region_compact : IsCompact region
  iqCarrier : Submodule ℚ (C3LogShellTensorBlock C3)
  iqCarrier_eq : iqCarrier = actualC3LogShellTensorIQ C3
  haar : Measure (C3LogShellTensorBlock C3)
  haar_eq : haar = actualC3LogShellTensorHaar C3
  haar_isAddHaar : Measure.IsAddHaarMeasure haar

/-- The actual candidate local LGP tensor packet at a bad place, built from the
actual C3 tensor packet data. -/
noncomputable def lgpBadLocalPacketCandidate
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (b : Bad (nativePlaceSelection T)) :
    LGPBadLocalPacketCandidate T C3 e b where
  region := lgpBadLocalPacketRegion T C3 e b
  region_eq := rfl
  region_compact := lgpBadLocalPacketRegion_compact T C3 e b
  iqCarrier := actualC3LogShellTensorIQ C3
  iqCarrier_eq := rfl
  haar := actualC3LogShellTensorHaar C3
  haar_eq := rfl
  haar_isAddHaar := inferInstance

/-- Under the injection data (e, indexEquiv, injection), the candidate packet
fiber at a bad place agrees with the all-place tensor fiber at the injected
all-place index. -/
theorem lgpBadLocalPacket_place_agree
    (e : Bad (nativePlaceSelection T) ≃ C3.tensorIndex)
    (indexEquiv : V ≃ C3.tensorIndex)
    (h : S3133BadToAllPlaceIndexInjection T C3 e indexEquiv)
    (b : Bad (nativePlaceSelection T)) :
    lgpBadLocalPacketFiber T C3 e b =
      C3LogShellFiber C3 (indexEquiv (h.badToV b)) := by
  unfold lgpBadLocalPacketFiber lgpBadTensorIndex
  rw [← h.index_agree b]

/-- Dimension positivity of the candidate local packet: transferred from the
actual C3 tensor packet dimension data. -/
theorem lgpLocalPacketDimension_pos : 0 < qPilotOneColumnDimension C3 :=
  qPilotOneColumnDimension_pos C3

/-- Exact identification data needed to identify the candidate with the paper's
local tensor packet IQ(A,alpha Fv) at v in V_bad (IUT III, Prop. 3.2, (ii),
pp. 97--99; Prop. 3.4, (ii), pp. 102--103; IUT II, Cor. 4.8).
* badTensorIndexEquivalence: the missing bad<->C3 tensor index equivalence
  (qpilot's S3131BadTensorIndexEquivalence; no total map exists in the tree);
* badToAllPlaceIndexInjection: the bad-to-all-place injection with index
  agreement (qpilot's S3133BadToAllPlaceIndexInjectionData);
* galoisActionOnPacket: the G_v(alpha Pi_v)-action on IQ(A,alpha Fv);
* labelComponents: the label-j components inside the tensor packets
  IQ(S^pm_{j+1,j}; Fv), j in {1,...,l*};
* logLinkCompatibility: compatibility with the log-link poly-isomorphisms. -/
structure LGPLocalPacketIdentificationMissing where
  badTensorIndexEquivalence : Prop
  badToAllPlaceIndexInjection : Prop
  galoisActionOnPacket : Prop
  labelComponents : Prop
  logLinkCompatibility : Prop

/-- The exact identification gap for the candidate local LGP tensor packet. -/
def LGPLocalPacketIdentificationGap : Prop :=
  Nonempty LGPLocalPacketIdentificationMissing

#check lgpBadTensorIndex
#check lgpBadLocalPacketFiber
#check lgpBadLocalPacketRegion_compact
#check lgpBadLocalPacketCandidate
#check lgpBadLocalPacket_place_agree
#check lgpLocalPacketDimension_pos
#check LGPLocalPacketIdentificationGap

end LeanFormal.IUT.XiFPaper.S3136LGPLocalTensorPacketActual
end