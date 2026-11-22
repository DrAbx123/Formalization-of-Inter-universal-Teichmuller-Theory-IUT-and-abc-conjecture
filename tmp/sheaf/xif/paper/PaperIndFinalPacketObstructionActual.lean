import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.PaperC3ThetaRootActual

-- S174 object audit: actual final tensor packet type and exact carrier
-- obstructions for Ind1/2/3 and for the root-valued theta image.
--
-- Actual facts checked:
-- * qVFamTensorBlock T b is a ONE-FACTOR completion tensor block
--   ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple;
-- * RootThetaCarrier is a product of units of ALGEBRAIC CLOSURES;
-- * no actual map from root-valued units to the completion block is present;
-- * actual Ind1/2/3 actions in the tree act on other carriers
--   (capsule tensor packets / TimesMuQuotient stages), not on qVFamTensorBlock.
-- This file records the exact missing object interfaces; no identity/action
-- is faked and no inequality is stated.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperIndFinalPacketObstructionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

universe u v

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

-- Actual final tensor packet at b.
abbrev FinalTensorPacket : Type :=
  qVFamTensorBlock T b

-- Actual root-valued theta carrier for a source geometry G.
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

-- Exact missing map: root theta units (algebraic closures) -> final completion
-- tensor packet.  A map would need an actual completion-root reduction; none is
-- present in the geometry.
structure RootThetaToFinalPacketMapGap where
  unitMap : RootThetaCarrier (G := G) → FinalTensorPacket T b
  image_compat : Prop
  completion_root_reduction : Prop

def RootThetaToFinalPacketMapGapRequired : Prop :=
  Nonempty (RootThetaToFinalPacketMapGap (T := T) (b := b) (G := G))

-- Exact missing Ind1/2/3 action objects on the final tensor packet.
structure IndActionsOnFinalPacketGap where
  carrier : Type (max u v)
  carrier_eq : carrier = FinalTensorPacket T b
  ind1 : carrier ≃ carrier
  ind2 : (v : V) → carrier ≃ carrier
  ind3 : Int → carrier → carrier
  rootThetaToCarrier : RootThetaCarrier (G := G) → carrier

def IndActionsOnFinalPacketGapRequired : Prop :=
  Nonempty (IndActionsOnFinalPacketGap (T := T) (b := b) (G := G))

-- Actual root-valued theta image set, for the object-level comparison.
noncomputable def rootThetaImageSet : Set (RootThetaCarrier (G := G)) :=
  Set.range (paperRootThetaImagePoint (G := G))

theorem rootThetaImageSet_mem (j : SignedLabel l.value) :
    paperRootThetaImagePoint (G := G) j ∈ rootThetaImageSet (G := G) :=
  ⟨j, rfl⟩

#check FinalTensorPacket
#check rootThetaImageSet
#check RootThetaToFinalPacketMapGap
#check IndActionsOnFinalPacketGap

end LeanFormal.IUT.XiFPaper.PaperIndFinalPacketObstructionActual

end