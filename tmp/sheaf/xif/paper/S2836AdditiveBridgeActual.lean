import tmp.sheaf.xif.paper.S2835HeightComparisonActual
import tmp.sheaf.xif.paper.S2833S2800HregionActual
import LeanFormal.IUT.ABCBridge.Bridge.Cor312ToABCBridgeInterface
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2800LineBundleCor312BridgeActual
open LeanFormal.IUT.XiFPaper.S2808S2800HalfNormalizedActual
open LeanFormal.IUT.XiFPaper.S2833S2800HregionActual
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
open LeanFormal.IUT.XiFPaper.S2781PointedLineBundleRegionActual
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000

namespace LeanFormal.IUT.XiFPaper.S2836AdditiveBridgeActual

abbrev S2836W : IQHullLogVolumeInterface (S2800Carrier S2833l) := S2808HalfIQHull S2833l 1

theorem S2836_hregion (eps : Real) (heps : 0 <= eps) :
    exists D : Real, forall a b c : Nat, IsABCTriple a b c ->
      (S2836W.logVolume (normalizedComparisonRegion S2836W
          (S2781LogShellPoint S2833l) a b c)).toReal
        <= (1 + eps) * arithmeticWeight (abcRationalPoint a c)
          + (S2836W.logVolume S2836W.hull).toReal + D := by
  refine ⟨(1 + eps) * S2792D, ?_⟩
  intro a b c habc
  change ((S2808HalfIQHull S2833l 1).logVolume
      (normalizedComparisonRegion (S2808HalfIQHull S2833l 1)
        (S2781LogShellPoint S2833l) a b c)).toReal
    <= (1 + eps) * arithmeticWeight (abcRationalPoint a c)
      + ((S2808HalfIQHull S2833l 1).logVolume
          (S2808HalfIQHull S2833l 1).hull).toReal
      + (1 + eps) * S2792D
  rw [S2833_region_volume a b c habc, S2833_hull_volume_zero]
  have hbase := S2792_regionVolume_le_weight_add_D a b c habc
  have hw0 : 0 <= arithmeticWeight (abcRationalPoint a c) := by
    rw [arithmeticWeight_abcRationalPoint habc]
    apply Real.log_nonneg
    exact_mod_cast Nat.succ_le_of_lt (natRadical_pos (a * b * c))
  have hD0 : 0 <= S2792D := by
    unfold S2792D
    have hlog : 0 < Real.log (((5 * 5 * 2161 * 2161 : Nat)) : Real) := by
      apply Real.log_pos
      norm_num
    exact le_of_lt (mul_pos (by norm_num : (0 : Real) < 1 / 2) hlog)
  nlinarith [hbase, heps, hw0, hD0]

noncomputable def S2836AdditiveComparison (eps A : Real)
    (hadd : forall a b c : Nat, IsABCTriple a b c ->
      Height.logHeight₁ (abcRationalPoint a c)
        <= (1 + eps) * (S2836W.logVolume
            (normalizedComparisonRegion S2836W (S2781LogShellPoint S2833l) a b c)).toReal
          + A) (heps : 0 <= eps) :
    Cor312EpsilonArithmeticComparisonAdditive S2836W eps A where
  logShellPoint := S2781LogShellPoint S2833l
  height_le_normalizedRegionVolume_add := hadd
  regionVolume_le_normalizedWeight := S2836_hregion eps heps

noncomputable def S2836AdditiveBridge
    (hadd : forall (eps : Real), 0 < eps ->
      exists A : Real, forall a b c : Nat, IsABCTriple a b c ->
        Height.logHeight₁ (abcRationalPoint a c)
          <= (1 + eps) * (S2836W.logVolume
              (normalizedComparisonRegion S2836W (S2781LogShellPoint S2833l) a b c)).toReal
            + A) :
    ABCHeightWeightAdditiveBoundV2 :=
  let Aeps : Real -> Real := fun eps =>
    if h : 0 < eps then Classical.choose (hadd eps h) else 0
  abcHeightWeightAdditiveBoundV2_of_epsilonComparisonAdditive
    S2836W Aeps
    (fun eps heps => by
      dsimp only [Aeps]
      rw [dif_pos heps]
      exact S2836AdditiveComparison eps
        (Classical.choose (hadd eps heps))
        (Classical.choose_spec (hadd eps heps)) (le_of_lt heps))

end LeanFormal.IUT.XiFPaper.S2836AdditiveBridgeActual
end
