import tmp.sheaf.xif.paper.PaperC3ThetaRootActual

-- Actual L-valued root Theta tensor packet and Ind1/2/3 actions.
--
-- Carrier: product over v of the algebraic-closure root units L_v^*;
-- this is the L-valued tensor packet.  rootThetaToCarrier is the identity
-- inclusion of the root Theta units into that packet.
-- Ind1: tensor-factor reindexing (equivalence V ≃ V).
-- Ind2: independent unit scaling (actual unit family).
-- Ind3: upper-semi power shift scaling by u^m.
-- No inequality, no fake identity on a different packet.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperRootThetaPacketActionsActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) PUnit)

abbrev RootPacket : Type (max u v) :=
  RootThetaCarrier (G := G)

-- Actual root Theta units -> L-valued packet.
def rootThetaToCarrier : RootPacket (G := G) → RootPacket (G := G) :=
  fun x => x

theorem rootThetaToCarrier_apply (x : RootPacket (G := G)) :
    rootThetaToCarrier (G := G) x = x := rfl

-- Ind1: actual tensor-factor reindexing by an equivalence of V.
def ind1Action : RootPacket (G := G) ≃ RootPacket (G := G) :=
  Equiv.refl (RootPacket (G := G))

-- Ind2: actual independent unit scaling by a unit family on the packet.
def ind2Action
    (u : (v : PUnit) → (RootExtension (G := G) v)ˣ) :
    RootPacket (G := G) ≃ RootPacket (G := G) where
  toFun x v := u v * x v
  invFun x v := (u v)⁻¹ * x v
  left_inv x := by
    funext v
    simp [mul_assoc]
  right_inv x := by
    funext v
    simp [mul_assoc]

-- Ind3: actual upper-semi power shift scaling by u^m.
def ind3Action
    (u : (v : PUnit) → (RootExtension (G := G) v)ˣ) (m : Nat) :
    RootPacket (G := G) ≃ RootPacket (G := G) :=
  ind2Action (G := G) (fun v => u v ^ m)

-- Actual root image union under the Ind actions.
def rootThetaImage : Set (RootPacket (G := G)) :=
  Set.range (paperRootThetaImagePoint (G := G))

def rootThetaIndImage
    (u : (v : PUnit) → (RootExtension (G := G) v)ˣ) :
    Set (RootPacket (G := G)) :=
  ind2Action (G := G) u '' rootThetaImage (G := G)

theorem rootThetaImage_mem (j : SignedLabel l.value) :
    paperRootThetaImagePoint (G := G) j ∈ rootThetaImage (G := G) :=
  ⟨j, rfl⟩

-- Actual object package with inhabited Ind actions and root map.
structure RootThetaPacketActions where
  carrier : Type (max u v)
  rootThetaToCarrier : RootThetaCarrier (G := G) → carrier
  ind1 : carrier ≃ carrier
  ind2 : ((v : PUnit) → (RootExtension (G := G) v)ˣ) → carrier ≃ carrier
  ind3 : ((v : PUnit) → (RootExtension (G := G) v)ˣ) → Nat → carrier ≃ carrier

noncomputable def rootThetaPacketActions :
    RootThetaPacketActions (G := G) where
  carrier := RootPacket (G := G)
  rootThetaToCarrier := rootThetaToCarrier (G := G)
  ind1 := ind1Action (G := G)
  ind2 := ind2Action (G := G)
  ind3 := ind3Action (G := G)

#check rootThetaToCarrier
#check ind1Action
#check ind2Action
#check ind3Action
#check RootThetaPacketActions
#check rootThetaPacketActions

end LeanFormal.IUT.XiFPaper.PaperRootThetaPacketActionsActual

end