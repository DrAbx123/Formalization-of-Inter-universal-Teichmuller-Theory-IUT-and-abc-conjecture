import tmp.sheaf.xif.paper.BadPlacePaperConstantsActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual

/-! # S640: root-normalized paper theta procession

Uses the existing 2l normalization:
  paperThetaCoefficient T b j = j^2 * order(q_v)/(2l),
and the existing uniform procession weights `processionLabelWeight`.
The procession value is the signed root-normalized theta log
  paperThetaCoefficient T b j * log p_b,
which is `-log |q[2u]^(j^2)|` (q[2u] = q[1u]^(1/(2l))).
No `realThetaValue q j = q^(j^2)` is used.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S640PaperRootThetaProcessionActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.BadPlacePaperConstantsActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))

/-- A procession unit label as a signed theta label. -/
noncomputable def processionSignedLabel (x : ProcessionLabel l) : SignedLabel l.value :=
  SignedLabel.representative l (x : Fl l.value)

/-- Root-normalized paper theta procession at a bad place. -/
noncomputable def paperRootThetaProcession :
    WeightedValues (ProcessionLabel l) where
  value x :=
    paperThetaCoefficient T b (processionSignedLabel (l := l) x) *
      Real.log (qVFamTensorP T b : Real)
  weight _ := processionLabelWeight (l := l)
  weightTotal := 1
  weightTotal_pos := by norm_num
  weightTotal_eq_sum := by
    simpa using (processionLabelWeight_total (l := l)).symm

theorem paperRootThetaProcession_weight_nonneg (x : ProcessionLabel l) :
    0 ≤ (paperRootThetaProcession T b).weight x :=
  inv_nonneg.mpr (Nat.cast_nonneg _)

theorem paperRootThetaProcession_value_eq_paperThetaCoefficient
    (x : ProcessionLabel l) :
    (paperRootThetaProcession T b).value x =
      paperThetaCoefficient T b (processionSignedLabel (l := l) x) *
        Real.log (qVFamTensorP T b : Real) := by
  rfl

theorem paperRootThetaProcession_average :
    (paperRootThetaProcession T b).average =
      ∑ x : ProcessionLabel l,
        processionLabelWeight (l := l) *
          (paperThetaCoefficient T b (processionSignedLabel (l := l) x) *
            Real.log (qVFamTensorP T b : Real)) := by
  unfold WeightedValues.average
  rw [paperRootThetaProcession]
  simp

theorem paperRootThetaProcession_average_nonneg :
    0 ≤ (paperRootThetaProcession T b).average := by
  apply WeightedValues.lower_le_average_of_pointwise
  · intro x
    exact paperRootThetaProcession_weight_nonneg (l := l) T b x
  · intro x
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (div_nonneg (Nat.cast_nonneg _) (by positivity)))
      (Real.log_nonneg (by exact_mod_cast (qVFamTensorP_pos T b)))

/-- The same actual procession is the one supplied to `PaperSignedHull.procession`. -/
noncomputable def paperSignedHullProcession :
    WeightedValues (ProcessionLabel l) :=
  paperRootThetaProcession T b

theorem paperSignedHullProcession_eq :
    paperSignedHullProcession T b = paperRootThetaProcession T b := rfl

/-- Root power used by the procession: the actual root is raised to j^2. -/
theorem paperRootThetaProcession_root_power
    (x : ProcessionLabel l) :
    qVFamPaperThetaValueRoot T b (processionSignedLabel (l := l) x) =
      (hodgeTwoLthRoot T b) ^
        (gaussExponent (processionSignedLabel (l := l) x).1).toNat :=
  qVFamPaperThetaValueRoot_formula T b (processionSignedLabel (l := l) x)

end LeanFormal.IUT.XiFPaper.S640PaperRootThetaProcessionActualAdapted
end
