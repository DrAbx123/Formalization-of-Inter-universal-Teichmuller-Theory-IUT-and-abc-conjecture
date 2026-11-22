import tmp.sheaf.xif.paper.RootNormalizedThetaHullActualAdapted
import tmp.sheaf.xif.PaperSignedHull

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S645RootNormalizedPaperSignedHullActualAdapted
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.RootNormalizedThetaHullActualAdapted
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory
open scoped BigOperators

universe uX
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

noncomputable def rootThetaSignedProcession :
    WeightedValues (SignedLabel l.value) where
  value j := - (∑ _ : qVFamTensorV, qVFamPaperThetaTensorCoefficient T b j) *
    Real.log (qVFamP T b : Real)
  weight _ := (Fintype.card (SignedLabel l.value) : Real)⁻¹
  weightTotal := 1
  weightTotal_pos := by norm_num
  weightTotal_eq_sum := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have hcard : (Fintype.card (SignedLabel l.value) : Real) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    exact (mul_inv_cancel₀ hcard).symm

theorem rootThetaSignedProcession_value (j : SignedLabel l.value) :
    (rootThetaSignedProcession T b).value j =
      - (∑ _ : qVFamTensorV, qVFamPaperThetaTensorCoefficient T b j) *
        Real.log (qVFamP T b : Real) := rfl

noncomputable def rootThetaSignedFiniteHull :
    FiniteHull (SignedLabel l.value) where
  volume j := (rootThetaSignedProcession T b).value j
  hullVolume := Finset.sum Finset.univ
    (fun j : SignedLabel l.value => |(rootThetaSignedProcession T b).value j|)
  contains j := by
    calc
      (rootThetaSignedProcession T b).value j <=
          |(rootThetaSignedProcession T b).value j| := le_abs_self _
      _ <= Finset.sum Finset.univ
            (fun i : SignedLabel l.value =>
              |(rootThetaSignedProcession T b).value i|) :=
        Finset.single_le_sum
          (fun i _ => abs_nonneg ((rootThetaSignedProcession T b).value i))
          (Finset.mem_univ j)

noncomputable def rootNormalizedPaperSignedHull
    {X : Type uX} (A : IQHullLogVolumeInterface X)
    (haverage : 0 <= (rootThetaSignedProcession T b).average)
    (hnormal : A.logVolume A.hull = ENNReal.ofReal
      (rootThetaSignedProcession T b).average) :
    PaperSignedHull X (SignedLabel l.value) where
  ambient := A
  procession := rootThetaSignedProcession T b
  hull := rootThetaSignedFiniteHull T b
  weighted_matches_hull := by
    intro j
    rfl
  weights_nonnegative := by
    intro _
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  average_nonneg := haverage
  hull_logVolume_eq_average := hnormal

theorem rootNormalizedPaperSignedHull_signed_eq
    {X : Type uX} (A : IQHullLogVolumeInterface X)
    (haverage : 0 <= (rootThetaSignedProcession T b).average)
    (hnormal : A.logVolume A.hull = ENNReal.ofReal
      (rootThetaSignedProcession T b).average) :
    (rootNormalizedPaperSignedHull T b A haverage hnormal).signedHullLogVolume =
      -(rootThetaSignedProcession T b).average := by
  unfold PaperSignedHull.signedHullLogVolume rootNormalizedPaperSignedHull
  rw [hnormal, ENNReal.toReal_ofReal haverage]

def RootThetaProcessionNormAlignment : Prop :=
  ∀ j : SignedLabel l.value,
    (rootThetaSignedProcession T b).value j =
      Real.log ‖(qVFamPaperThetaValueRoot T b j :
        AlgebraicClosure (Completion (qVPlace T b)))‖

end LeanFormal.IUT.XiFPaper.S645RootNormalizedPaperSignedHullActualAdapted
end