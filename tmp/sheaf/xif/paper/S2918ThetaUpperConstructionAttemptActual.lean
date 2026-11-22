import tmp.sheaf.xif.paper.S2838HeightComparisonReductionActual
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual
import tmp.sheaf.xif.paper.S2752FinalHweightvolActual
import tmp.sheaf.xif.paper.S2780LineBundleABCBridgeActual
import LeanFormal.IUT.ABCBridge.Arithmetic.ABCHeightArithmeticWeightComparison
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2838HeightComparisonReductionActual
open LeanFormal.IUT.XiFPaper.S2780LineBundleABCBridgeActual
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaper.S2792NormalizedLineBundleBridge
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2918ThetaUpperConstructionAttemptActual

/-- Unhalved theta/J upper gap: the honest inequality obtained from an ABC
height-weight additive bound, because the actual S2752 weight bound is
`weight ≤ S2780RegionVolume` (unhalved). -/
def S2918UnhalvedThetaUpperGap (eps AJ : Real) : Prop :=
  forall a b c : Nat, IsABCTriple a b c ->
    Height.logHeight₁ (abcJInvariant a b c) <=
      6 * (1 + eps) * S2780RegionVolume a b c + AJ

/-- Actual conditional construction: an ABC height-weight additive bound
implies the unhalved theta/J upper gap.  No `hadd` for the line-bundle bridge
is assumed; `h` is the ABC-equivalent arithmetic contract. -/
theorem S2918_unhalvedThetaUpperGap_of_additive
    (h : ABCHeightWeightAdditiveBoundV2) (eps : Real) (heps : 0 < eps) :
    exists AJ : Real, S2918UnhalvedThetaUpperGap eps AJ := by
  obtain ⟨A, hA⟩ := ABCHeightWeightAdditiveBoundV2.exists_constant h heps
  refine ⟨6 * A + Real.log 256, ?_⟩
  intro a b c habc
  have hJ := (abcJInvariant_logHeight_bounds_abcRationalPoint habc).2
  have hh := hA a b c habc
  have hw : arithmeticWeight (abcRationalPoint a c) <= S2780RegionVolume a b c := by
    simpa [S2780RegionVolume] using
      S2752_hweightvol fiveLabel a b c habc
  have hcoef : 0 <= 1 + eps := by linarith
  nlinarith [hJ, hh, hw, hcoef]

/-- The halved S2838 gap follows from the unhalved gap at the doubled
epsilon, since `S2780RegionVolume = 2 * S2792RegionVolume`. -/
theorem S2918_s2838ThetaUpperGap_of_unhalved
    (eps AJ : Real) (h : S2918UnhalvedThetaUpperGap eps AJ) :
    exists eps' : Real, exists AJ' : Real, S2838ThetaUpperGap eps' AJ' := by
  refine ⟨1 + 2 * eps, AJ, ?_⟩
  intro a b c habc
  have h' := h a b c habc
  have hhalved : S2780RegionVolume a b c = 2 * S2792RegionVolume a b c := by
    unfold S2792RegionVolume
    ring
  have hcoef : 6 * (1 + (1 + 2 * eps)) = 6 * (1 + eps) * 2 := by ring
  rw [hhalved] at h'
  nlinarith [h', hcoef]

/-- Conditional construction of the exact S2838 object from the
ABC-equivalent additive contract. -/
theorem S2918_s2838ThetaUpperGap_of_additive
    (h : ABCHeightWeightAdditiveBoundV2) (eps : Real) (heps : 0 < eps) :
    exists eps' : Real, exists AJ' : Real, S2838ThetaUpperGap eps' AJ' := by
  obtain ⟨AJ, hAJ⟩ := S2918_unhalvedThetaUpperGap_of_additive h eps heps
  exact S2918_s2838ThetaUpperGap_of_unhalved eps AJ hAJ

#check S2918UnhalvedThetaUpperGap
#check S2918_unhalvedThetaUpperGap_of_additive
#check S2918_s2838ThetaUpperGap_of_additive
#print axioms S2918_s2838ThetaUpperGap_of_additive

end LeanFormal.IUT.XiFPaper.S2918ThetaUpperConstructionAttemptActual
end
