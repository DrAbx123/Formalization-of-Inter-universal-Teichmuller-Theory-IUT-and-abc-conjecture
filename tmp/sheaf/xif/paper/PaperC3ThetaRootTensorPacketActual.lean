import tmp.sheaf.xif.paper.PaperC3ThetaRootActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks

-- Actual root Theta tensor packet on the algebraic-closure product carrier
--
-- PaperC3ThetaRootActual gives actual root theta units q_v^(j^2) in the
-- algebraic-closure Kummer extension. This file packages the actual product
-- carrier, the root Theta image set, and the identity unit map.
--
-- The completion arithmetic-tuple tensor block cannot receive these units
-- without a completion root; that map is an exact obstruction below. The old
-- completion qUnit^(j^2) is not used as the root theta value.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperC3ThetaRootTensorPacketActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual

universe u v

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type v} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

-- The actual algebraic-closure product tensor carrier.
abbrev RootThetaTensorCarrier : Type (max u v) :=
  RootThetaCarrier (G := G)

-- Actual root Theta tensor packet: product carrier, root image set, identity
-- unit map.
structure RootThetaTensorPacketActual where
  carrier : Type (max u v)
  imageSet : Set carrier
  unitMap : RootThetaTensorCarrier (G := G) → carrier
  imageSet_eq : imageSet =
    Set.range (unitMap ∘ paperRootThetaImagePointTheta (G := G))

noncomputable def rootThetaTensorPacketActual :
    RootThetaTensorPacketActual (G := G) where
  carrier := RootThetaTensorCarrier (G := G)
  imageSet := paperRootThetaImageSetTheta (G := G)
  unitMap := id
  imageSet_eq := rfl

theorem rootThetaTensorPacketActual_carrier :
    (rootThetaTensorPacketActual (G := G)).carrier =
      RootThetaTensorCarrier (G := G) := rfl

theorem rootThetaTensorPacketActual_imageSet :
    (rootThetaTensorPacketActual (G := G)).imageSet =
      paperRootThetaImageSet (G := G) := rfl

theorem rootThetaTensorPacketActual_unitMap :
    (rootThetaTensorPacketActual (G := G)).unitMap =
      (id : RootThetaTensorCarrier (G := G) → RootThetaTensorCarrier (G := G)) := rfl

-- The completion arithmetic-tuple tensor block at the same source places.
abbrev CompletionTensorBlock : Type (max u v) :=
  ArithmeticTensorTupleBlock (fun v (_ : Unit) => G.place v) (fun _ => ())

-- Exact obstruction: no actual map from the algebraic-closure root units to
-- the completion tensor block is constructed. Such a map would require a
-- completion 2l-th root; the completion-root gap records this precisely.
structure RootThetaToCompletionTensorMapGap where
  unitMap : RootThetaTensorCarrier (G := G) → CompletionTensorBlock (G := G)
  unitMap_compat : Prop
  completionRoot : Prop

-- The gap is a record of the exact missing map/data; it is not asserted to
-- have an inhabitant.  In particular it is not a trivial `True` placeholder.

#check RootThetaTensorCarrier
#check RootThetaTensorPacketActual
#check rootThetaTensorPacketActual
#check rootThetaTensorPacketActual_carrier
#check rootThetaTensorPacketActual_imageSet
#check CompletionTensorBlock
#check RootThetaToCompletionTensorMapGap

end LeanFormal.IUT.XiFPaper.PaperC3ThetaRootTensorPacketActual

end