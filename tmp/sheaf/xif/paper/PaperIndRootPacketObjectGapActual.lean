import tmp.sheaf.xif.paper.PaperC3RootThetaHullActual
import tmp.sheaf.xif.paper.PaperC3ThetaRootTensorPacketActual

-- Object-level Theta image union on the root product carrier, and exact
-- carrier gaps for Ind1/2/3 on the final tensor packet / λO hull.
-- No inequality; no fake hull/scaling/packet.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperIndRootPacketObjectGapActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.PaperC3RootThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootTensorPacketActual

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

-- Actual possible Theta image union over nonzero labels and mu_{2l}.
noncomputable def ThetaPossibleImageUnion : Set (RootThetaCarrier (G := G)) :=
  paperRootThetaHull (G := G)

theorem thetaLabelRootPoint_mem_union
    (j : ThetaLabel (l := l)) :
    paperRootThetaMuPoint (G := G) 0 (thetaLabelToSigned (l := l) j) ∈
      ThetaPossibleImageUnion (G := G) :=
  paperRootThetaHull_mem (G := G) j 0

-- Exact missing Ind1/2/3 actions on the final tensor packet.
structure IndActionsOnFinalPacketGap where
  carrier : Type (max u v)
  ind1 : carrier ≃ carrier
  ind2 : (v : V) → carrier ≃ carrier
  ind3 : Int → carrier → carrier
  rootThetaToCarrier : RootThetaCarrier (G := G) → carrier

def IndActionsOnFinalPacketGapRequired : Prop :=
  Nonempty (IndActionsOnFinalPacketGap (G := G))

-- Exact missing λO/scaling hull object: the mu union is actual; the λO hull
-- equality is not asserted.
structure ThetaHolomorphicHullGap where
  hull : Set (RootThetaCarrier (G := G))
  hull_eq_union : Prop
  hull_eq_scaling_region : Prop

def ThetaHolomorphicHullGapRequired : Prop :=
  Nonempty (ThetaHolomorphicHullGap (G := G))

#check ThetaPossibleImageUnion
#check thetaLabelRootPoint_mem_union
#check IndActionsOnFinalPacketGap
#check ThetaHolomorphicHullGap

end LeanFormal.IUT.XiFPaper.PaperIndRootPacketObjectGapActual

end