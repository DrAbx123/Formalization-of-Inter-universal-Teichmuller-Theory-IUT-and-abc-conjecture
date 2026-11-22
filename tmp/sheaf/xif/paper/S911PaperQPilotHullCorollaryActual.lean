import tmp.sheaf.xif.paper.S814SkeletonQuantizedLeastHullActual
import tmp.sheaf.xif.paper.S814PaperHullLogInterfaceActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.S813PaperInterfaceHub

-- S911: W2 skeleton corollary direction audit.
-- W2 gives skeleton(-ord logp) <= hull log.  Paper qPilot is
-- -cRoot logp >= skeleton; the corollary paperQPilot <= hull needs
-- cRoot realized in the value group (ceil(cRoot)=cRoot).

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S911PaperQPilotHullCorollaryActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S814SkeletonQuantizedLeastHullActual
open LeanFormal.IUT.XiFPaper.S814PaperHullLogInterfaceActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S813PaperInterfaceHub
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))
variable (μ : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure μ]

theorem paperRootCoefficientFamily_sum_eq :
    (∑ _ : qVFamTensorV, paperRootCoefficientFamily T b ()) =
      ((qVFamily T b).order : Real) / (2 * (l.value : Real)) := by
  simp [paperRootCoefficientFamily, qVFamPaperRootCoefficient, Finset.sum_const,
    qVFamTensorV, nsmul_eq_mul]

/-- W2's skeleton lower bound: -order log p <= hull log. -/
theorem paperSkeletonQPilotLog_le_hull :
    paperSkeletonQPilotLog (l := l) T b μ ≤
      paperLeastLambdaOHullLog (l := l) T b μ :=
  paperSkeletonQPilotLog_le_paperLeastLambdaOHullLog (l := l) T b μ

/-- The skeleton log is <= the paper qPilot log (cRoot <= order). -/
theorem paperSkeletonQPilotLog_le_paperQPilotLogLeast :
    paperSkeletonQPilotLog (l := l) T b μ ≤
      paperQPilotLogLeast (l := l) T b := by
  rw [paperSkeletonQPilotLog_eq (l := l) T b μ]
  unfold paperQPilotLogLeast
  rw [paperRootCoefficientFamily_sum_eq (l := l) T b]
  have hlog : 0 < Real.log (qVFamTensorP T b : Real) :=
    Real.log_pos (by exact_mod_cast
      (Fact.out (p := Nat.Prime (qVFamTensorP T b))).one_lt)
  have h2l : (1 : Real) ≤ 2 * (l.value : Real) := by
    have h5 : (5 : Real) ≤ l.value := by exact_mod_cast l.ge_five
    nlinarith
  have hpos : 0 < 2 * (l.value : Real) := by positivity
  have ho : 0 ≤ ((qVFamily T b).order : Real) := Nat.cast_nonneg _
  have hle : ((qVFamily T b).order : Real) / (2 * (l.value : Real)) ≤
      ((qVFamily T b).order : Real) := by
    calc ((qVFamily T b).order : Real) / (2 * (l.value : Real)) ≤
          ((qVFamily T b).order : Real) / 1 := by
          exact div_le_div_of_nonneg_left ho zero_lt_one h2l
      _ = ((qVFamily T b).order : Real) := div_one _
  have hmul := mul_le_mul_of_nonneg_right hle hlog.le
  linarith

/-- Exact condition: the hull log is the unquantized paper value. -/
def PaperQPilotHullExactCondition : Prop :=
  paperLeastLambdaOHullLog (l := l) T b μ =
    -((∑ _ : qVFamTensorV, paperRootCoefficientFamily T b ()) *
      Real.log (qVFamTensorP T b : Real))

theorem paperQPilotLogLeast_le_hull_of_exactCondition
    (h : PaperQPilotHullExactCondition (l := l) T b μ) :
    paperQPilotLogLeast (l := l) T b ≤ paperLeastLambdaOHullLog (l := l) T b μ := by
  rw [h]
  unfold paperQPilotLogLeast
  exact le_rfl

/-- Exact value-group realization of cRoot: local generators of the paper norm. -/
def PaperCoefficientValueGroupRealized : Prop :=
  ∃ g : (i : qVFamTensorV) →
      CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)),
    ∀ i, ‖g i‖ = (qVFamTensorP T b : Real) ^
      (-(paperRootCoefficientFamily T b i))

theorem exactCondition_of_valueGroupRealized
    (h : PaperCoefficientValueGroupRealized (l := l) T b) :
    PaperQPilotHullExactCondition (l := l) T b μ := by
  rcases h with ⟨g, hg⟩
  unfold PaperQPilotHullExactCondition
  exact paperLeastLambdaOHullLog_eq_neg_sum_of_quantized_generator
    (l := l) T b μ (paperRootCoefficientFamily T b) rfl g hg

theorem paperQPilotLogLeast_le_hull_of_valueGroupRealized
    (h : PaperCoefficientValueGroupRealized (l := l) T b) :
    paperQPilotLogLeast (l := l) T b ≤ paperLeastLambdaOHullLog (l := l) T b μ :=
  paperQPilotLogLeast_le_hull_of_exactCondition (l := l) T b μ
    (exactCondition_of_valueGroupRealized (l := l) T b μ h)

/-- Fill S814's interface without a data parameter, under value-group realization. -/
noncomputable def paperHullLogInterfaceOfValueGroupRealized
    (h : PaperCoefficientValueGroupRealized (l := l) T b) :
    PaperHullLogInterface (qVFamTensorBlock T b) :=
  paperHullLogInterfaceOfLogLe (l := l) T b μ
    (paperQPilotLogLeast_le_hull_of_valueGroupRealized (l := l) T b μ h)

/-- Strict quantization: if cRoot is not realized and the hull uses c' > cRoot,
the paper corollary is false. -/
theorem paperQPilotLeHull_false_of_strict_quantization
    (c' : qVFamTensorV → Real)
    (hball : arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
        qVFamTensorTuple c' =
      arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperRootCoefficientFamily T b))
    (hstrict : ∀ i, paperRootCoefficientFamily T b i < c' i)
    (g : (i : qVFamTensorV) →
      CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)))
    (hg : ∀ i, ‖g i‖ = (qVFamTensorP T b : Real) ^ (-(c' i))) :
    ¬ paperQPilotLogLeast (l := l) T b ≤ paperLeastLambdaOHullLog (l := l) T b μ := by
  have hlt := paperLeastLambdaOHullLog_lt_neg_sum_of_strict_quantization
    (l := l) T b μ c' hball hstrict g hg
  intro hle
  unfold paperQPilotLogLeast at hle
  linarith

#check paperSkeletonQPilotLog_le_hull
#check paperSkeletonQPilotLog_le_paperQPilotLogLeast
#check paperQPilotLogLeast_le_hull_of_valueGroupRealized
#check paperHullLogInterfaceOfValueGroupRealized
#check paperQPilotLeHull_false_of_strict_quantization

end LeanFormal.IUT.XiFPaper.S911PaperQPilotHullCorollaryActual

end