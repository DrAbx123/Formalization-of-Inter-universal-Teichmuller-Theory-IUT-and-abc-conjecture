import Mathlib
import tmp.sheaf.xif.paper.S3131CoefficientGapActual
import tmp.sheaf.xif.paper.S826CNormOrderRamificationActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientOrderAuditActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual
import tmp.sheaf.xif.paper.QVFamPureFractionalScalingDataGapActual
import tmp.sheaf.xif.paper.S778PaperQPilotHalfRegionActual

/-! # S3131: task-13 coefficient normalization verdict

Source determination (IUT III Remark 3.1.1, (ii), corpus lines 5408-5465;
Proposition 3.9, (i), corpus lines 6838-6893; IUT IV Proposition 1.4, (i)):
the paper's local log-volume is normalized so that multiplication by the
rational prime p adds -log p (packet-normalization), i.e. it is the
Q_p-spectral normalization ||p|| = p^{-1}, and it is degree-normalized by the
local degree (IUT IV Prop 1.4(i) = arithmeticTupleNormalizedLogVolume).  The
paper-faithful local q coefficient is therefore

  c_norm = -logb_p ||q||_spectral = order / e        (tree theorem: S826),

and the paper-faithful rooted (2l-th root) coefficient is

  rootHalfCoefficient = c_norm / (2l)                (S778/S3131),

NOT the tree's S805/S779 qVFamPaperRootCoefficient, which is order/(2l) in the
classical-discrete-order (default residue norm) convention.  The two differ by
the local ramification index e: qVFamPaperRootCoefficient = e * rootHalfCoefficient
under the tree's normalized norm relation.  Hence the S3131 coefficient
comparison (paperRoot <= c_norm) is equivalent to the local ramification bound
e <= 2l, an explicit arithmetic property of the fixed input C, not a consequence
of the abstract source data.

Verdicts (all reduced to actual real statements, nothing assumed):
* comparison paperRoot <= c_norm  <->  e <= 2l   (S3131CoefficientComparison_iff_ramification);
  it can fail whenever e > 2l.  So do NOT build the paper comparison on the
  S805/S779 convention; the paper-faithful choice is rootHalfCoefficient, for
  which the rooted q-pilot region / rooted Theta hull comparison is the already
  actual S778 qPilotPaperLog_le_thetaLog (unconditional, same coefficient).
* native identification gap c_norm = c_pure  <->  e * L = 1, where
  L = log(residueNormBase)/log p > 0 (c_pure = order*L is tree theorem
  QVFamNormalizedCoefficientOrderAuditActual.qVFamDefaultCoefficient_eq_order_mul).
  Since e >= 1 and L >= 1 this forces e = 1 and L = 1: the gap is not a general
  identity and is false for any input with e > 1 or f > 1.  It needs the actual
  local arithmetic of C; the abstract source data do not force it.

No sorry/axiom/True/PUnit; no coefficient is redefined by hand here (the paper
choice is the tree's already actual c_norm/rootHalfCoefficient). -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3131CoefficientReductionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientOrderAuditActual
open LeanFormal.IUT.XiFPaper.S826CNormOrderRamificationActual
open LeanFormal.IUT.XiFPaper.S3131CoefficientGapActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.S778PaperQPilotHalfRegionActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [forall b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [forall b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The paper root coefficient is order(q)/(2l) by definition. -/
theorem S3131PaperRootCoefficient_eq :
    qVFamPaperRootCoefficient (l := l) T b =
      ((qVFamily T b).order : Real) / (2 * (l.value : Real)) := rfl

/-- The canonical (default-residue-norm) coefficient is the pure coefficient. -/
theorem S3131DefaultCoefficient_eq_pureCoefficient :
    qVFamDefaultCoefficient (l := l) T b = qVFamPureCoefficient T b () := by
  simp [qVFamDefaultCoefficient, qVFamPureCoefficient, qVFamDefaultCompletionUnit]

/-- The normalized (Q_p-spectral) root coefficient at the single tensor factor
is c_norm. -/
theorem S3131RootNormCoefficient_eq :
    rootNormCoefficient (l := l) T b () = qVFamNormalizedCoefficient T b := rfl

/-- The rooted paper-faithful coefficient is c_norm/(2l). -/
theorem S3131RootHalfCoefficient_eq :
    rootHalfCoefficient (l := l) T b () =
      qVFamNormalizedCoefficient T b / (2 * (l.value : Real)) := rfl

/-- **Task-13 reduction (comparison).** Under the tree's normalized norm
relation at the relative ramification index e, the S3131 coefficient comparison
paperRoot <= c_norm is exactly the local ramification bound e <= 2l. -/
theorem S3131CoefficientComparison_iff_ramification
    (e : Real) (hepos : 0 < e)
    (hcomp : QVFamNormalizedNormCompatibility (l := l) T b e) :
    S3131CoefficientComparisonRequired (l := l) T b ↔ e ≤ 2 * (l.value : Real) := by
  have hcn : qVFamNormalizedCoefficient T b = ((qVFamily T b).order : Real) / e :=
    qVFamNormalizedCoefficient_eq_order_div_e (l := l) T b e hcomp
  have hord : (0 : Real) < ((qVFamily T b).order : Real) :=
    by exact_mod_cast (qVFamily T b).order_pos
  have h2l : (0 : Real) < 2 * (l.value : Real) := by
    have h5 : (5 : Real) ≤ (l.value : Real) := by exact_mod_cast l.ge_five
    linarith
  rw [S3131CoefficientComparisonRequired_iff]
  rw [S3131PaperRootCoefficient_eq, hcn]
  constructor
  · intro h
    rw [div_le_div_iff₀ h2l hepos] at h
    exact le_of_mul_le_mul_left h hord
  · intro h
    rw [div_le_div_iff₀ h2l hepos]
    exact mul_le_mul_of_nonneg_left h hord.le

/-- **Task-13 verdict (comparison can fail).** If the local ramification index
exceeds 2l, the S3131 coefficient comparison is false.  So the comparison is
not a theorem of the abstract source data. -/
theorem S3131CoefficientComparison_false_of_ramification_gt
    (e : Real) (hepos : 0 < e)
    (hcomp : QVFamNormalizedNormCompatibility (l := l) T b e)
    (hgt : 2 * (l.value : Real) < e) :
    ¬ S3131CoefficientComparisonRequired (l := l) T b := by
  intro h
  have hle := (S3131CoefficientComparison_iff_ramification (l := l) T b e hepos hcomp).mp h
  linarith

/-- **Task-13 correction of the coefficient choice.** The tree's S805/S779
"paper root coefficient" order/(2l) is e times the paper-faithful rooted
coefficient c_norm/(2l) = rootHalfCoefficient under the normalized norm
relation.  Hence the paper-faithful choice is rootHalfCoefficient (S778), not
the S805/S779 order/(2l). -/
theorem S3131PaperRootCoefficient_eq_ramification_mul_rootHalf
    (e : Real) (hepos : 0 < e)
    (hcomp : QVFamNormalizedNormCompatibility (l := l) T b e) :
    qVFamPaperRootCoefficient (l := l) T b =
      e * rootHalfCoefficient (l := l) T b () := by
  have hcn : qVFamNormalizedCoefficient T b = ((qVFamily T b).order : Real) / e :=
    qVFamNormalizedCoefficient_eq_order_div_e (l := l) T b e hcomp
  have h2l : (0 : Real) < 2 * (l.value : Real) := by
    have h5 : (5 : Real) ≤ (l.value : Real) := by exact_mod_cast l.ge_five
    linarith
  rw [S3131PaperRootCoefficient_eq, S3131RootHalfCoefficient_eq, hcn]
  field_simp [ne_of_gt hepos, ne_of_gt h2l]

/-- **Task-13 reduction (native identification gap).** Under the normalized norm
relation, c_norm = c_pure is exactly e * L = 1 with
L = log(residueNormBase)/log p, i.e. the ramification index times the local
residue-degree-in-p-log units equals one. -/
theorem S3131NormalizedCoefficientGap_iff_ramification_mul_log
    (e : Real) (hepos : 0 < e)
    (hcomp : QVFamNormalizedNormCompatibility (l := l) T b e) :
    QVFamNormalizedCoefficientGap (l := l) T b ↔
      e * (Real.log (residueNormBase (qVFamTensorPlace (l := l) T b)) /
        Real.log (qVFamTensorP (l := l) T b : Real)) = 1 := by
  have hcn : qVFamNormalizedCoefficient T b = ((qVFamily T b).order : Real) / e :=
    qVFamNormalizedCoefficient_eq_order_div_e (l := l) T b e hcomp
  have hcp : qVFamPureCoefficient T b () =
      ((qVFamily T b).order : Real) *
        (Real.log (residueNormBase (qVFamTensorPlace (l := l) T b)) /
          Real.log (qVFamTensorP (l := l) T b : Real)) := by
    rw [← S3131DefaultCoefficient_eq_pureCoefficient (l := l) T b]
    exact qVFamDefaultCoefficient_eq_order_mul (l := l) T b
  have hord : (0 : Real) < ((qVFamily T b).order : Real) :=
    by exact_mod_cast (qVFamily T b).order_pos
  unfold QVFamNormalizedCoefficientGap
  rw [hcn, hcp]
  set L : Real :=
    Real.log (residueNormBase (qVFamTensorPlace (l := l) T b)) /
      Real.log (qVFamTensorP (l := l) T b : Real) with hL
  constructor
  · intro h
    have h1 : ((qVFamily T b).order : Real) =
        ((qVFamily T b).order : Real) * (L * e) := by
      calc ((qVFamily T b).order : Real) =
            (((qVFamily T b).order : Real) / e) * e := (div_mul_cancel₀ _ (ne_of_gt hepos)).symm
        _ = (((qVFamily T b).order : Real) * L) * e := by rw [h]
        _ = ((qVFamily T b).order : Real) * (L * e) := by ring
    have hone : (1 : Real) = L * e :=
      mul_left_cancel₀ (ne_of_gt hord) (by rw [mul_one]; exact h1)
    rw [mul_comm]
    exact hone.symm
  · intro h
    have hLval : L = 1 / e := by
      rw [eq_div_iff (ne_of_gt hepos)]
      simpa [mul_comm] using h
    rw [hLval]
    field_simp [ne_of_gt hepos]

/-- **Task-13 verdict (native gap can fail).** If e * L != 1 then the registered
native identification gap c_norm = c_pure is false.  In particular the abstract
source data do not force it; it is input arithmetic. -/
theorem S3131NormalizedCoefficientGap_false_of
    (e : Real) (hepos : 0 < e)
    (hcomp : QVFamNormalizedNormCompatibility (l := l) T b e)
    (h : e * (Real.log (residueNormBase (qVFamTensorPlace (l := l) T b)) /
        Real.log (qVFamTensorP (l := l) T b : Real)) ≠ 1) :
    ¬ QVFamNormalizedCoefficientGap (l := l) T b := by
  intro hgap
  exact h ((S3131NormalizedCoefficientGap_iff_ramification_mul_log
    (l := l) T b e hepos hcomp).mp hgap)

/-- **Paper-faithful actual comparison (corrected coefficient choice).** With
the paper-faithful rooted coefficient rootHalfCoefficient on both sides, the
actual q-pilot region readout is at most the actual rooted Theta hull readout
(S778 actual containment and monotonicity), unconditionally. -/
theorem S3131PaperFaithfulRootedComparison
    [MeasurableSpace (qVFamTensorBlock T b)]
    [BorelSpace (qVFamTensorBlock T b)]
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] :
    qPilotPaperLog (l := l) T b mu ≤
      rootThetaHullLog (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple mu
        (rootHalfCoefficient (l := l) T b) :=
  qPilotPaperLog_le_thetaLog (l := l) T b mu

/-! ## Paper-faithful global weighted comparison at the corrected rooted
spectral coefficient -/

variable [forall b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [forall b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]
variable (mu : forall b : Bad (nativePlaceSelection T),
  Measure (qVFamTensorBlock T b))
variable [forall b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]

/-- The actual Remark 3.1.1(ii) place weight is nonnegative. -/
theorem S3131CoefficientWeight_nonneg (b : Bad (nativePlaceSelection T)) :
    0 ≤ nativeBadLocalWeight T b := by
  rw [nativeBadLocalWeight_eq_inv]
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- **Paper-faithful Batch A comparison (corrected coefficient), weighted.**  With
the rooted Q_p-spectral coefficient rootHalfCoefficient = c_norm/(2l) on both
sides, the weighted procession-normalized q-pilot region readout is at most the
weighted rooted Theta-hull readout, unconditionally: it is the actual S778
containment/monotonicity comparison summed with the actual nonnegative place
weights.  No coefficient comparison gap and no norm-instance gap enters. -/
theorem S3131PaperFaithfulRegionalRootedComparison :
    (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * qPilotPaperLog (l := l) T b (mu b)) ≤
      (∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b *
          rootThetaHullLog (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
            (mu b) (rootHalfCoefficient (l := l) T b)) := by
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left
    (S3131PaperFaithfulRootedComparison (l := l) T b (mu b))
    (S3131CoefficientWeight_nonneg (l := l) T b)

#check S3131CoefficientComparison_iff_ramification
#check S3131CoefficientComparison_false_of_ramification_gt
#check S3131PaperRootCoefficient_eq_ramification_mul_rootHalf
#check S3131NormalizedCoefficientGap_iff_ramification_mul_log
#check S3131NormalizedCoefficientGap_false_of
#check S3131PaperFaithfulRootedComparison

end LeanFormal.IUT.XiFPaper.S3131CoefficientReductionActual

end
