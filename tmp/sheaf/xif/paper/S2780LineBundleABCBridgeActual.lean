import tmp.sheaf.xif.paper.S2752FinalHweightvolActual
import tmp.sheaf.xif.paper.S2754LineBundleBridgeInterfaceActual
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual
import tmp.sheaf.xif.paper.S2736QPilotLineBundleHweightvol
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.S2736QPilotLineBundleHweightvol
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2780LineBundleABCBridgeActual

/-- The line-bundle region volume used by the bridge (varies with the triple). -/
noncomputable def S2780RegionVolume (a b c : Nat) : Real :=
  S2736QPilotLineBundleLogVolume (l := fiveLabel)
    (S2752J fiveLabel a b c)

/-- Explicit height gap: logHeight bounded by (1+eps) times the line-bundle
region volume of the triple.  No proof is stored. -/
def S2780HeightGap (eps : Real) : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    Height.logHeight₁ (abcRationalPoint a c) <=
      (1 + eps) * S2780RegionVolume a b c

/-- Explicit region/weight gap with an additive constant D. -/
def S2780RegionWeightGap (eps : Real) : Prop :=
  exists D : Real, forall a b c : Nat, IsABCTriple a b c ->
    (1 + eps) * S2780RegionVolume a b c <=
      (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D

/-- Conditional line-bundle ABC bridge data. -/
structure S2780LineBundleABCBridge (eps : Real) where
  height_gap : S2780HeightGap eps
  region_weight_gap : S2780RegionWeightGap eps

/-- hweightvol is the actual S2752 statement (witness that the line-bundle
region volume is the qPilot line-bundle volume). -/
theorem S2780_hweightvol :
    S2736QPilotLineBundleHweightvol (l := fiveLabel) (S2752J fiveLabel) 0 :=
  S2752_hweightvol fiveLabel

/-- Consumption theorem: height bound for ABC triples from the conditional
line-bundle bridge. -/
theorem S2780_heightBound_of_bridge (eps : Real)
    (B : S2780LineBundleABCBridge eps) :
    exists D : Real, forall a b c : Nat, IsABCTriple a b c ->
      Height.logHeight₁ (abcRationalPoint a c) <=
        (1 + eps) * arithmeticWeight (abcRationalPoint a c) + D := by
  obtain ⟨D, hD⟩ := B.region_weight_gap
  refine ⟨D, ?_⟩
  intro a b c habc
  have h1 := B.height_gap a b c habc
  have h2 := hD a b c habc
  exact le_trans h1 h2

end LeanFormal.IUT.XiFPaper.S2780LineBundleABCBridgeActual
end
