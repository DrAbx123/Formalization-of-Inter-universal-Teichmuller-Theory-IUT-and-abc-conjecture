import tmp.sheaf.xif.PaperSignedHull
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual
import tmp.sheaf.xif.paper.PaperThetaProcessionNormalizedLogActual

/-! # S657: independent root signed hull sign correction

Uses the actual `qVFamTensorP T b` (no stale `qVFamP`).  The positive
root theta magnitude is `+ coefficient * log(qVFamTensorP)`, so its average
is nonnegative and can fill `PaperSignedHull.average_nonneg`. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S657RootSignedHullIndependentActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open MeasureTheory

universe uX
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Positive root-normalized theta magnitude coefficient. -/
noncomputable def rootThetaMagnitudeValue (j : SignedLabel l.value) : Real :=
  (∑ _ : qVFamTensorV, qVFamPaperThetaTensorCoefficient T b j) *
    Real.log (qVFamTensorP T b : Real)

theorem rootThetaMagnitudeValue_nonneg (j : SignedLabel l.value) :
    0 <= rootThetaMagnitudeValue T b j := by
  unfold rootThetaMagnitudeValue
  have hcoeff : 0 <= ∑ _ : qVFamTensorV, qVFamPaperThetaTensorCoefficient T b j := by
    apply Finset.sum_nonneg
    intro _ _
    unfold qVFamPaperThetaTensorCoefficient qVFamPaperRootCoefficient
    positivity
  have hlog : 0 < Real.log (qVFamTensorP T b : Real) := by
    have hp : (1 : Real) < (qVFamTensorP T b : Real) := by
      exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt
    exact Real.log_pos hp
  exact mul_nonneg hcoeff hlog.le

noncomputable def rootThetaMagnitudeProcession :
    WeightedValues (SignedLabel l.value) where
  value := rootThetaMagnitudeValue T b
  weight _ := (Fintype.card (SignedLabel l.value) : Real)⁻¹
  weightTotal := 1
  weightTotal_pos := by norm_num
  weightTotal_eq_sum := by
    letI : Nonempty (SignedLabel l.value) :=
      ⟨SignedLabel.representative l (0 : Fl l.value)⟩
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have hcardNat : 0 < Fintype.card (SignedLabel l.value) :=
      Fintype.card_pos_iff.mpr inferInstance
    have hcard : (Fintype.card (SignedLabel l.value) : Real) ≠ 0 := by
      exact_mod_cast ne_of_gt hcardNat
    exact (mul_inv_cancel₀ hcard).symm

theorem rootThetaMagnitudeProcession_average_nonneg :
    0 <= (rootThetaMagnitudeProcession T b).average := by
  unfold WeightedValues.average rootThetaMagnitudeProcession
  rw [div_one]
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact rootThetaMagnitudeValue_nonneg T b j

noncomputable def rootThetaMagnitudeFiniteHull :
    FiniteHull (SignedLabel l.value) where
  volume j := rootThetaMagnitudeValue T b j
  hullVolume := Finset.sum Finset.univ
    (fun j : SignedLabel l.value => |rootThetaMagnitudeValue T b j|)
  contains j := by
    calc
      rootThetaMagnitudeValue T b j <= |rootThetaMagnitudeValue T b j| :=
        le_abs_self _
      _ <= Finset.sum Finset.univ
            (fun i : SignedLabel l.value => |rootThetaMagnitudeValue T b i|) :=
        Finset.single_le_sum
          (fun i _ => abs_nonneg (rootThetaMagnitudeValue T b i))
          (Finset.mem_univ j)

/-- Corrected actual signed hull with provable average_nonneg. -/
noncomputable def rootNormalizedPaperSignedHullCorrected
    {X : Type uX} (A : IQHullLogVolumeInterface X)
    (hnormal : A.logVolume A.hull = ENNReal.ofReal
      (rootThetaMagnitudeProcession T b).average) :
    PaperSignedHull X (SignedLabel l.value) where
  ambient := A
  procession := rootThetaMagnitudeProcession T b
  hull := rootThetaMagnitudeFiniteHull T b
  weighted_matches_hull := by intro j; rfl
  weights_nonnegative := by intro _; exact inv_nonneg.mpr (Nat.cast_nonneg _)
  average_nonneg := rootThetaMagnitudeProcession_average_nonneg T b
  hull_logVolume_eq_average := hnormal

theorem rootNormalizedPaperSignedHullCorrected_signed_eq
    {X : Type uX} (A : IQHullLogVolumeInterface X)
    (hnormal : A.logVolume A.hull = ENNReal.ofReal
      (rootThetaMagnitudeProcession T b).average) :
    (rootNormalizedPaperSignedHullCorrected T b A hnormal).signedHullLogVolume =
      -(rootThetaMagnitudeProcession T b).average := by
  unfold PaperSignedHull.signedHullLogVolume rootNormalizedPaperSignedHullCorrected
  rw [hnormal, ENNReal.toReal_ofReal (rootThetaMagnitudeProcession_average_nonneg T b)]

end LeanFormal.IUT.XiFPaper.S657RootSignedHullIndependentActual

end
