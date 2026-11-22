import tmp.sheaf.xif.paper.S2808S2800HalfNormalizedActual
import tmp.sheaf.xif.paper.S2792NormalizedLineBundleBridge
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open scoped ENNReal nonZeroDivisors Classical Pointwise
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2800LineBundleCor312BridgeActual
open LeanFormal.IUT.XiFPaper.S2781PointedLineBundleRegionActual
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
open LeanFormal.IUT.XiFPaper.S2808S2800HalfNormalizedActual
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaper.S2780LineBundleABCBridgeActual
open LeanFormal.IUT.XiFPaper.S2736QPilotLineBundleHweightvol
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000

namespace LeanFormal.IUT.XiFPaper.S2833S2800HregionActual

abbrev S2833l : PrimeGeFive := fiveLabel

theorem S2833_cov_one : S2808CovolumeLog S2833l (1 : S2800Carrier S2833l) = 0 := by
  unfold S2808CovolumeLog S2781CovolumeLog
  rw [show ((1 : S2800Carrier S2833l).1) = (1 : FractionalIdeal (nonZeroDivisors (SourceOK (A := S2735Arithmetic S2833l))) (S2735Arithmetic S2833l).K) from rfl]
  rw [FractionalIdeal.absNorm_one]
  norm_num

theorem S2833_cov_point_eq (a b c : Nat) (habc : IsABCTriple a b c) :
    S2808CovolumeLog S2833l (S2781LogShellPoint S2833l a b c)
      = S2780RegionVolume a b c := by
  unfold S2808CovolumeLog S2781CovolumeLog S2781LogShellPoint S2781QPilotPoint
  by_cases h : qPilotLineBundleExtended (l := S2833l) (S2752J S2833l a b c) = 0
  · rw [dif_pos h]
    have h' : qPilotLineBundleExtended (l := S2833l) (S2752J S2833l a b c) = 0 := h
    simp only [S2780RegionVolume, S2833l, S2736QPilotLineBundleLogVolume, h']
    rw [show ((1 : S2800Carrier S2833l).1) = (1 : FractionalIdeal _ _) from rfl]
    rw [FractionalIdeal.absNorm_one]
    norm_num
  · rw [dif_neg h]
    rfl

theorem S2833_s_nonneg (a b c : Nat) (habc : IsABCTriple a b c) :
    0 <= S2780RegionVolume a b c := by
  have hw : arithmeticWeight (abcRationalPoint a c) <= S2780RegionVolume a b c := by
    simpa [S2780RegionVolume, S2833l] using S2752_hweightvol S2833l a b c habc
  have hw0 : 0 <= arithmeticWeight (abcRationalPoint a c) := by
    rw [arithmeticWeight_abcRationalPoint habc]
    apply Real.log_nonneg
    exact_mod_cast Nat.succ_le_of_lt (natRadical_pos (a * b * c))
  linarith

theorem S2833_pair_volume (a b c : Nat) (habc : IsABCTriple a b c) :
    S2808LogVolume S2833l
      (({1} : Set (S2800Carrier S2833l)) ∪ {S2781LogShellPoint S2833l a b c})
      = ENNReal.ofReal ((1 / 2) * S2780RegionVolume a b c) := by
  have hs := S2833_s_nonneg a b c habc
  have hcov := S2833_cov_point_eq a b c habc
  apply le_antisymm
  · refine iSup_le fun y => ?_
    have hy' : y.1 = (1 : S2800Carrier S2833l) ∨ y.1 = S2781LogShellPoint S2833l a b c := by
      have hmem : y.1 ∈ (({1} : Set (S2800Carrier S2833l)) ∪ {S2781LogShellPoint S2833l a b c}) := y.2
      rw [Set.mem_union] at hmem
      simpa using hmem
    rcases hy' with hy | hy
    · rw [hy, S2833_cov_one]
      simp only [mul_zero, ENNReal.ofReal_zero]
      exact bot_le
    · rw [hy, hcov]
  · have hmem : S2781LogShellPoint S2833l a b c ∈
        (({1} : Set (S2800Carrier S2833l)) ∪ {S2781LogShellPoint S2833l a b c}) := by simp
    rw [← hcov]
    exact le_iSup (fun y : ↥(({1} : Set (S2800Carrier S2833l)) ∪ {S2781LogShellPoint S2833l a b c}) =>
      ENNReal.ofReal ((1 / 2) * S2808CovolumeLog S2833l y.1)) ⟨S2781LogShellPoint S2833l a b c, hmem⟩

theorem S2833_region_volume (a b c : Nat) (habc : IsABCTriple a b c) :
    ((S2808HalfIQHull S2833l 1).logVolume
        (normalizedComparisonRegion (S2808HalfIQHull S2833l 1)
          (S2781LogShellPoint S2833l) a b c)).toReal
      = S2792RegionVolume a b c := by
  simp only [normalizedComparisonRegion, S2808HalfIQHull, Set.image_id]
  rw [S2833_pair_volume a b c habc]
  rw [ENNReal.toReal_ofReal]
  · unfold S2792RegionVolume
    ring
  · nlinarith [S2833_s_nonneg a b c habc]

theorem S2833_hull_volume_zero :
    ((S2808HalfIQHull S2833l 1).logVolume
        (S2808HalfIQHull S2833l 1).hull).toReal = 0 := by
  show (S2808LogVolume S2833l ({1} : Set (S2800Carrier S2833l))).toReal = 0
  have h : S2808LogVolume S2833l ({1} : Set (S2800Carrier S2833l)) = 0 := by
    apply le_antisymm
    · refine iSup_le fun y => ?_
      rw [Set.mem_singleton_iff.mp y.2, S2833_cov_one]
      simp
    · exact bot_le
  rw [h, ENNReal.toReal_zero]

noncomputable def S2833EpsData (eps : Real) (heps : 0 <= eps)
    (hheight : forall a b c : Nat, IsABCTriple a b c ->
      Height.logHeight₁ (abcRationalPoint a c)
        <= (1 + eps) * ((S2808HalfIQHull S2833l 1).logVolume
            (normalizedComparisonRegion (S2808HalfIQHull S2833l 1)
              (S2781LogShellPoint S2833l) a b c)).toReal) :
    S2800EpsData S2833l (S2808Global S2833l) eps := by
  obtain ⟨D, hD⟩ := S2792RegionWeightGap_actual eps heps
  refine ⟨?_, hheight⟩
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

end LeanFormal.IUT.XiFPaper.S2833S2800HregionActual
end
