import tmp.sheaf.xif.paper.Mzk1ScaledThetaHullScalingShaActual
import tmp.sheaf.xif.paper.Mzk1HullLogVolumeFormulaActual
import tmp.sheaf.xif.paper.S1915ThetaHullA0Actual
import tmp.sheaf.xif.paper.Mzk1ShellArithmeticIdentitiesActual
import Mathlib.Tactic

/-!
# A779 scaled θ-hull: unconditional normalized-log identity (shehdd)

Corrects/strengthens the conditional dictionary in `Mzk1ScaledPaper312Actual`:
`rootExtensionProductNormalizedLog` is relative to the unit ball and does NOT
include the S1902 `+1`; hence the exact identity is

  `rootExtensionProductNormalizedLog (scaledThetaHull k) = scaledClosedFormR k - 1`,

NOT `= scaledClosedFormR k`.  Proved here unconditionally from
* `scaledThetaHull_log_toReal` (iterated Haar scaling law, A775-1);
* `s1915_log_normalized_hull` and the S1902 normalization formula.

Consequences proved:
* `normalizedLog_full_eq`: full-region normalized log = `s1915ClosedForm - 1`;
* `scaledThetaHull_normalizedLog_eq`: the scaled identity above;
* `scaledStatement_iff_closedForm`: the scaled paper statement is
  `qReading ≤ scaledClosedFormR k - 1` (unconditional equivalence on the S1902 carrier).

The remaining A779 dictionary (`(sFactor(nC)-1)·A ≤ V_paper`) is still PENDING
(needs the procession/archimedean and c_lana dictionary), and is NOT asserted.
No RETRACTED statement is used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullNormalizedLogShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullScalingShaActual
open LeanFormal.IUT.XiFPaper.Mzk1HullLogVolumeFormulaActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.Mzk1ShellArithmeticIdentitiesActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Full-region normalized log (relative to the unit ball) equals `s1915ClosedForm - 1`. -/
theorem normalizedLog_full_eq :
    rootExtensionProductNormalizedLog T (fullRegion T) =
      s1915ClosedForm T - 1 := by
  have hfullpos : 0 < rootExtensionProductHaar T (fullRegion T) :=
    fullRegion_measure_pos' T
  have hfullfin : rootExtensionProductHaar T (fullRegion T) < ⊤ :=
    fullRegion_measure_lt_top' T
  obtain ⟨hupos, hufin⟩ := rootExtensionProductHaar_unitBall_pos_lt_top (T := T)
  have hraw : 0 < (rootExtensionProductHaar T (fullRegion T)).toReal :=
    ENNReal.toReal_pos (ne_of_gt hfullpos) (ne_of_lt hfullfin)
  have hunit : 0 < (rootExtensionProductHaar T
      (rootExtensionProductUnitBall T)).toReal :=
    ENNReal.toReal_pos (ne_of_gt hupos) (ne_of_lt hufin)
  have h := s1915_log_normalized_hull T
  rw [s1902NormalizedHaar_apply_toReal] at h
  have hunit_eq : s1902UnitRegion T = rootExtensionProductUnitBall T := rfl
  rw [hunit_eq, ← fullRegion_eq_hull T] at h
  have hreassoc :
      Real.exp 1 * (rootExtensionProductHaar T (fullRegion T)).toReal /
          (rootExtensionProductHaar T (rootExtensionProductUnitBall T)).toReal =
        Real.exp 1 * ((rootExtensionProductHaar T (fullRegion T)).toReal /
          (rootExtensionProductHaar T (rootExtensionProductUnitBall T)).toReal) := by
    ring
  rw [hreassoc] at h
  rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity), Real.log_exp,
    Real.log_div (ne_of_gt hraw) (ne_of_gt hunit)] at h
  unfold rootExtensionProductNormalizedLog
  linarith
/-- **Exact normalized log of the scaled θ-hull**: `scaledClosedFormR k - 1`. -/
theorem scaledThetaHull_normalizedLog_eq (k : ℕ) :
    rootExtensionProductNormalizedLog T (scaledThetaHull T k) =
      scaledClosedFormR T k - 1 := by
  have hfull := normalizedLog_full_eq T
  unfold rootExtensionProductNormalizedLog at hfull ⊢
  rw [scaledThetaHull_log_toReal]
  rw [scaledClosedFormR_eq]
  linarith

/-- The scaled paper statement with the correct normalized log dictionary. -/
def ScaledPaper312Statement (qReading : ℝ) (k : ℕ) : Prop :=
  qReading ≤ rootExtensionProductNormalizedLog T (scaledThetaHull T k)

/-- **Unconditional equivalence to the corrected closed form**:
`qReading ≤ scaledClosedFormR k - 1`. -/
theorem scaledStatement_iff_closedForm (qReading : ℝ) (k : ℕ) :
    ScaledPaper312Statement T qReading k ↔
      qReading ≤ scaledClosedFormR T k - 1 := by
  unfold ScaledPaper312Statement
  rw [scaledThetaHull_normalizedLog_eq]

structure CorrectedRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def correctedRows : List CorrectedRow :=
  [ ⟨"full normalized log", "normalizedLog fullRegion = s1915ClosedForm - 1", "PROVED"⟩
  , ⟨"scaled normalized log", "normalizedLog (scaledThetaHull k) = scaledClosedFormR k - 1", "PROVED (unconditional)"⟩
  , ⟨"statement equivalence", "ScaledPaper312Statement qReading k <-> qReading <= scaledClosedFormR k - 1", "PROVED (unconditional)"⟩
  , ⟨"off-by-one correction", "normalized log does NOT include the S1902 +1; hull's hlog must use scaledClosedFormR k - 1", "CORRECTION"⟩
  , ⟨"remaining A779 dictionary", "(sFactor(nC)-1).A <= V_paper (procession/archimedean/c_lana)", "PENDING"⟩
  , ⟨"scope", "no RETRACTED use; no fake coefficient equivalence", "INTEGRITY"⟩
  ]

theorem correctedRows_length : correctedRows.length = 6 := rfl

theorem correctedRows_has_pending :
    correctedRows.any (fun r => r.status = "PENDING") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullNormalizedLogShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullNormalizedLogShaActual.normalizedLog_full_eq
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullNormalizedLogShaActual.scaledThetaHull_normalizedLog_eq
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullNormalizedLogShaActual.scaledStatement_iff_closedForm
