/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HullLogVolumeFormulaActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionThetaHullAuditActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import Mathlib.Tactic

/-! # CONDITIONAL exact hull V upper bound (#7)

Exact product formula gives normalizedLog(hull) = sum_b (log mu_ball_b - log mu_unit_b).
To get V <= (1/4) l (log d + log f) + C0, this file takes the missing local/arithmetic
bounds as explicit named data.  No inhabitant is constructed; this is an addressable
GAP interface, not progress.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ExactHullVUpperBoundActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1HullLogVolumeFormulaActual
open MeasureTheory
open scoped BigOperators

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

instance badNonempty : Nonempty (Bad (nativePlaceSelection T)) := by
  rcases (nativePlaceSelection T).V_mod_bad_nonempty with ⟨p, hp⟩
  exact ⟨⟨p, hp⟩⟩

/-- Named local and arithmetic bounds needed for the paper V upper bound. -/
structure HullVUpperBoundData where
  log_d : Real
  log_f : Real
  C0 : Real
  localBound : Bad (nativePlaceSelection T) → Real
  local_le : ∀ b, (Real.log (rootExtensionHaar T b
      (Metric.closedBall (0 : rootNormedExtension T b)
        ((rootImageRadius T b : NNReal) : Real))).toReal -
      Real.log (rootExtensionHaar T b (rootExtensionUnitBall T b)).toReal) ≤ localBound b
  sum_le : (∑ b : Bad (nativePlaceSelection T), localBound b) ≤
    (1 / 4 : Real) * (l.value : Real) * (log_d + log_f) + C0

theorem normalizedLog_hull_le_of_data
    (D : HullVUpperBoundData (T := T)) :
    rootExtensionProductNormalizedLog T (s1902Hull T) ≤
      (1 / 4 : Real) * (l.value : Real) * (D.log_d + D.log_f) + D.C0 := by
  rw [normalizedLog_hull_eq_sum_diff]
  exact (Finset.sum_le_sum (fun b _ => D.local_le b)).trans D.sum_le

def HullVUpperBoundRequired : Prop := Nonempty (HullVUpperBoundData (T := T))

def rows : List (String × String × String) :=
  [ ("exact product log", "sum_b log mu(ball rootImageRadius_b)", "GREEN (Mzk1HullLogVolumeFormulaActual)"),
    ("local_le", "per-place log mu(ball) - log mu(unit) bound", "NAMED INPUT"),
    ("sum_le", "sum localBound <= (1/4)l(log d+log f)+C0", "NAMED INPUT"),
    ("normalizedLog_hull_le_of_data", "conditional V upper bound", "PROVED CONDITIONAL"),
    ("C0 source", "no actual C0 object in tree", "GAP") ]

theorem rows_length : rows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ExactHullVUpperBoundActual

end