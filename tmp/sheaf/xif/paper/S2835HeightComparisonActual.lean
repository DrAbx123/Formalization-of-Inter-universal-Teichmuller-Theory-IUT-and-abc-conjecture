import tmp.sheaf.xif.paper.S2833S2800HregionActual
import tmp.sheaf.xif.paper.S2834BridgeWithHeightActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ComparisonGapReduction
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2800LineBundleCor312BridgeActual
open LeanFormal.IUT.XiFPaper.S2808S2800HalfNormalizedActual
open LeanFormal.IUT.XiFPaper.S2833S2800HregionActual
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
open LeanFormal.IUT.XiFPaper.S2780LineBundleABCBridgeActual
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaper.S2781PointedLineBundleRegionActual
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000

namespace LeanFormal.IUT.XiFPaper.S2835HeightComparisonActual

abbrev S2835W : IQHullLogVolumeInterface (S2800Carrier S2833l) := S2808HalfIQHull S2833l 1

/-- The additive IUT IV height comparison fragment (version-2 shape) for the
half-normalized pointed region.  This is the exact missing height object; it is
NOT derived from carrier fields (the multiplicative V1 form is refuted). -/
def S2835HeightRegionComparison (eps A : Real) : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    Height.logHeight₁ (abcRationalPoint a c)
      <= (1 + eps) * (S2835W.logVolume
          (normalizedComparisonRegion S2835W (S2781LogShellPoint S2833l) a b c)).toReal
        + A

/-- From the additive height bound and the weight/region comparison one gets
the additive height/region comparison fragment (actual conditional assembly). -/
theorem S2835_additiveComparison_of_weight_bound
    {eps A : Real} (heps : 0 <= eps)
    (hadd : forall a b c : Nat, IsABCTriple a b c ->
      Height.logHeight₁ (abcRationalPoint a c)
        <= (1 + eps) * arithmeticWeight (abcRationalPoint a c) + A)
    (hweightvol : forall a b c : Nat, IsABCTriple a b c ->
      arithmeticWeight (abcRationalPoint a c)
        <= (S2835W.logVolume
            (normalizedComparisonRegion S2835W (S2781LogShellPoint S2833l) a b c)).toReal) :
    S2835HeightRegionComparison eps A :=
  cor312Gap1_height_le_normalizedRegionVolume_of_additiveBound
    S2835W (S2781LogShellPoint S2833l) heps hadd hweightvol

/-- The non-additive height gap (hheight) is the A = 0 specialization. -/
theorem S2835_hheight_of_zero_A (eps : Real) (heps : 0 <= eps)
    (h : S2835HeightRegionComparison eps 0) :
    forall a b c : Nat, IsABCTriple a b c ->
      Height.logHeight₁ (abcRationalPoint a c)
        <= (1 + eps) * (S2835W.logVolume
            (normalizedComparisonRegion S2835W (S2781LogShellPoint S2833l) a b c)).toReal := by
  intro a b c habc
  have := h a b c habc
  linarith

/-- Weight is bounded by twice the half-normalized region volume (from S2752 /
S2780 half normalization).  Hence the height comparison needs the *unhalved*
region volume, or a factor 2 absorption. -/
theorem S2835_weight_le_two_regionVolume
    (a b c : Nat) (habc : IsABCTriple a b c) :
    arithmeticWeight (abcRationalPoint a c)
      <= 2 * S2792RegionVolume a b c := by
  have h : arithmeticWeight (abcRationalPoint a c) <= S2780RegionVolume a b c := by
    simpa [S2780RegionVolume, S2833l] using S2752_hweightvol S2833l a b c habc
  have h2 : S2780RegionVolume a b c = 2 * S2792RegionVolume a b c := by
    unfold S2792RegionVolume
    ring
  linarith

end LeanFormal.IUT.XiFPaper.S2835HeightComparisonActual
end
