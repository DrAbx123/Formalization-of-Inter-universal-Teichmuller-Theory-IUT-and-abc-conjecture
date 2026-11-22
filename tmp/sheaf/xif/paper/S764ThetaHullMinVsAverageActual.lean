import tmp.sheaf.xif.paper.S694ThetaAverageNormalizationActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual

/-! # S764: paper Theta-pilot hull log: hull-min vs S694 label average

IUT III Remark 3.9.5(i): the paper hull is a lambda * O hull.  At the
one-factor qVFamily block the hull-min exponent is j = 1, namely
c_hull = order/(2l).  The S694 procession average over the l* positive
labels is a different scalar with coefficient (l+1)/24.  This file keeps
both actual formulas separate; the hull-min is the paper hull log.

No equality between the two is asserted, and no zero-inclusive hull is used.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S764ThetaHullMinVsAverageActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- hull-min coefficient at the one-factor paper qVFamily block: order/(2l). -/
noncomputable def paperThetaHullMinCoefficient : Real :=
  1 / (2 * (l.value : Real))

/-- S694 label-average coefficient: (1/l*) sum_{j=1}^{l*} j^2/(2l) = (l+1)/24. -/
noncomputable def paperThetaAverageCoefficient : Real :=
  ((l.value : Real) + 1) / 24

/-- Per-b paper Theta-pilot hull log (hull-min, negative signed log). -/
noncomputable def paperThetaHullMinLog (b : Bad (nativePlaceSelection T)) : Real :=
  -(((qVFamily T b).order : Real) * paperThetaHullMinCoefficient (l := l) *
    Real.log (qVFamTensorP T b : Real))

/-- Per-b S694 procession-average Theta log (NOT the hull log). -/
noncomputable def paperThetaAverageLog (b : Bad (nativePlaceSelection T)) : Real :=
  -(((qVFamily T b).order : Real) * paperThetaAverageCoefficient (l := l) *
    Real.log (qVFamTensorP T b : Real))

/-- Global hull-min paper Theta-pilot log, native bad-place weights. -/
noncomputable def globalPaperThetaHullMinLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * paperThetaHullMinLog (l := l) T b

/-- Global S694 average Theta log (NOT the hull log). -/
noncomputable def globalPaperThetaAverageLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * paperThetaAverageLog (l := l) T b

/-- The hull-min log is exactly the one-factor paper root formula log. -/
theorem paperThetaHullMinLog_eq_paperRootThetaFormulaLog :
    paperThetaHullMinLog (l := l) T b =
      paperRootThetaFormulaLog (l := l) T b := by
  unfold paperThetaHullMinLog paperThetaHullMinCoefficient
    paperRootThetaFormulaLog qVFamPaperRootCoefficient
  rw [Finset.sum_const, Finset.card_univ, Finset.card_univ]
  norm_num
  ring

theorem paperThetaHullMinCoefficient_lt_averageCoefficient :
    paperThetaHullMinCoefficient (l := l) <
      paperThetaAverageCoefficient (l := l) := by
  have h5 : (5 : Real) ≤ (l.value : Real) := by exact_mod_cast l.ge_five
  unfold paperThetaHullMinCoefficient paperThetaAverageCoefficient
  have hl : (0 : Real) < (l.value : Real) := by positivity
  field_simp [hl]
  nlinarith

theorem paperThetaHullMinLog_gt_averageLog
    (horder : 0 < ((qVFamily T b).order : Real))
    (hlog : 0 < Real.log (qVFamTensorP T b : Real)) :
    paperThetaHullMinLog (l := l) T b >
      paperThetaAverageLog (l := l) T b := by
  have hcoef := paperThetaHullMinCoefficient_lt_averageCoefficient (l := l)
  have hpos : 0 < ((qVFamily T b).order : Real) *
      Real.log (qVFamTensorP T b : Real) := mul_pos horder hlog
  unfold paperThetaHullMinLog paperThetaAverageLog
  nlinarith [mul_lt_mul_of_pos_left hcoef hpos]

/-- The global hull-min log is the weighted sum of the per-b hull-min logs. -/
theorem globalPaperThetaHullMinLog_eq :
    globalPaperThetaHullMinLog (l := l) T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * paperThetaHullMinLog (l := l) T b := rfl

/-- The global S694 average log is the weighted sum of the per-b averages. -/
theorem globalPaperThetaAverageLog_eq :
    globalPaperThetaAverageLog (l := l) T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * paperThetaAverageLog (l := l) T b := rfl

/-- Exact bridge from the current root-hull log to the paper hull-min log.
This is the nonzero-label hull + PaperRootHullFormulaGap bridge; it is not
asserted. -/
def PaperThetaHullMinBridge : Prop :=
  paperRootThetaHullLog (l := l) T b Measure.addHaar =
    paperThetaHullMinLog (l := l) T b

/-- The S694 average log is not the paper hull log: the hull-min coefficient is
strictly smaller, so (for positive order/log) the average log is strictly more
negative. -/
theorem paperThetaAverageLog_ne_hullMinLog
    (horder : 0 < ((qVFamily T b).order : Real))
    (hlog : 0 < Real.log (qVFamTensorP T b : Real)) :
    paperThetaAverageLog (l := l) T b ≠ paperThetaHullMinLog (l := l) T b :=
  ne_of_lt (paperThetaHullMinLog_gt_averageLog (l := l) T b horder hlog)

end LeanFormal.IUT.XiFPaper.S764ThetaHullMinVsAverageActual

end
