import tmp.sheaf.xif.paper.RootThetaExtensionHullCarrierActual

/-!
# Root/L Ind action transport: exact gap

Actual source-side actions exist in GlobalKummerIndActionsActual /
Ind1AutomorphismTensorActionActual / IndActionsThetaLinkActual.  They act on
ActualTensorPacket and ActualInd3Stage, not on the root/L carrier.

This file records the exact missing transport to the actual root theta carrier
and its image union.  No action is defined as identity or as an arbitrary
equivalence just to fill the gap.  No inequality is stated.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.RootThetaIndActionsGapActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.RootThetaExtensionHullCarrierActual

universe u v

variable {l : PrimeGeFive}
variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {V : Type} [Fintype V]
variable (G : CompletionValuedSourceGeometry (l := l) (K := K) (p := p) V)

/-- Actual root carrier chosen for possible Ind actions. -/
abbrev RootThetaIndCarrier : Type :=
  RootThetaExtensionCarrier (G := G)

/-- Actual root theta image union (mu orbits over positive labels). -/
noncomputable abbrev rootThetaIndImageUnion : Set (RootThetaIndCarrier (G := G)) :=
  rootThetaExtensionHull (G := G)

theorem rootThetaIndImageUnion_contains_image :
    rootThetaExtensionImageSet (G := G) ⊆ rootThetaIndImageUnion (G := G) :=
  rootThetaExtensionImage_subset_hull (G := G)

/-- Exact missing objects: transport from the source ActualTensorPacket to
the root carrier, and Ind1/2/3 actions on that carrier compatible with the
root image union. -/
structure RootThetaIndActionsGap where
  tensorPacketToRootCarrier : Prop
  ind1ActionOnRoot : Prop
  ind2ActionOnRoot : Prop
  ind3ActionOnRoot : Prop
  actionCompatibility : Prop
  imageUnionCompatibility : Prop

def RootThetaIndActionsGapRequired : Prop :=
  Nonempty RootThetaIndActionsGap

end LeanFormal.IUT.XiFPaper.RootThetaIndActionsGapActual
end
