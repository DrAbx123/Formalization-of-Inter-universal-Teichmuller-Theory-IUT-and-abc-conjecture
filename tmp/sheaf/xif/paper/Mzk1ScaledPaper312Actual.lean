/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ScaledThetaHullShaActual
import tmp.sheaf.xif.paper.Mzk1ShellArithmeticIdentitiesActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import Mathlib.Tactic

/-! # A779 hull: scaled θ-side paper statement

`paperThetaHullScaled T k` is shehdd's actual scaled θ-hull `scaledThetaHull T k`
on the real S1902 product carrier; `thetaScaledLog T k` is its actual normalized
log-volume.  The scaled paper statement is

  `ScaledPaper312Statement T qReading k := qReading <= thetaScaledLog T k`.

Proved: the definitional equivalence, the capsule average identity
`(1/n) Σ_j (j²-1) = sFactor(n)-1` (green), the j=1 capsule zero contribution,
and the conditional reduction to shehdd's closed form.  The *unconditional*
equivalence `ScaledPaper312Statement ↔ (sFactor-1)A <= V_paper` needs the
analytic identification `thetaScaledLog = scaledClosedFormR` (iterated Haar
scaling law; the recorded shehdd gap) and the V_paper definition; it is not
asserted here. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ScaledPaper312Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.Mzk1ScaledThetaHullShaActual
open LeanFormal.IUT.XiFPaper.Mzk1ShellArithmeticIdentitiesActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionThetaHullAuditActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open scoped BigOperators ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- The scaled θ-pilot hull on the real S1902 product carrier. -/
def paperThetaHullScaled (k : ℕ) : Set (S1902Carrier T) := scaledThetaHull T k

/-- The actual normalized log-volume of the scaled θ-hull. -/
noncomputable def thetaScaledLog (k : ℕ) : ℝ := 
  rootExtensionProductNormalizedLog T (paperThetaHullScaled T k)

/-- The scaled paper 3.12 statement: q reading at most the scaled θ-hull log. -/
def ScaledPaper312Statement (qReading : ℝ) (k : ℕ) : Prop :=
  qReading ≤ thetaScaledLog T k

theorem scaledPaper312Statement_iff (qReading : ℝ) (k : ℕ) :
    ScaledPaper312Statement T qReading k ↔ qReading ≤ thetaScaledLog T k := Iff.rfl

/-- The scaled hull is the actual full region at `k = 0`. -/
theorem paperThetaHullScaled_zero :
    paperThetaHullScaled T 0 = fullRegion T := by
  unfold paperThetaHullScaled
  exact scaledThetaHull_zero T

/-- Conditional reduction to shehdd's closed form.  The dictionary field is the
missing analytic identification `thetaScaledLog = scaledClosedFormR` (iterated
Haar scaling law), not a comparison. -/
theorem scaledPaper312_of_closedForm
    (qReading : ℝ) (k : ℕ)
    (hlog : thetaScaledLog T k = scaledClosedFormR T (k : ℝ))
    (hcomp : qReading ≤ scaledClosedFormR T (k : ℝ)) :
    ScaledPaper312Statement T qReading k := by
  unfold ScaledPaper312Statement
  rw [hlog]
  exact hcomp

/-- **j = 1 capsule is automatic**: the `(j²-1)` exponent vanishes at `j=1`. -/
theorem capsule_one_exponent_zero : (((1 : ℝ) ^ 2) - 1) = 0 := by norm_num

/-- **Capsule average identity** (green): `(1/n) Σ_j (j²-1) = sFactor n - 1`. -/
theorem capsule_average_identity (n : ℕ) (hn : 0 < n) :
    (1 / (n : ℝ)) * (∑ j ∈ Finset.range n, (((j : ℝ) + 1) ^ 2 - 1)) =
      sFactor n - 1 :=
  shell_average_identity n hn

/-- The scaled closed form in the `s1915 - k*S` form (shehdd, green). -/
theorem scaledClosedFormR_eq_s1915_sub (k : ℝ) :
    scaledClosedFormR T k = s1915ClosedForm T - k * qLogSum T :=
  scaledClosedFormR_eq T k

/-- Capsule-level comparison condition (abstract arithmetic): if the j-th
capsule contributes `(j²-1) * A_j` with `A_j >= 0` and the q reading is `-A`
(`A = Σ_j A_j`), then the j=1 capsule contributes zero and the comparison
reduces to the remaining capsules. -/
theorem scaledPaper312_iff_sum_condition
    (qReading : ℝ) (A : ℝ) (V : ℝ) (hq : qReading = -A)
    (hV : thetaScaledLog T 1 = V) :
    ScaledPaper312Statement T qReading 1 ↔ -A ≤ V := by
  unfold ScaledPaper312Statement
  rw [hq, hV]

def scaledPaperRows : List (String × String × String) :=
  [ ("scaled θ-hull", "paperThetaHullScaled k = scaledThetaHull k (real S1902 carrier)", "DEF"),
    ("scaled log", "thetaScaledLog k = normalized product log of the scaled hull", "DEF"),
    ("statement", "ScaledPaper312Statement qReading k := qReading <= thetaScaledLog k", "DEF"),
    ("k=0", "scaled hull = fullRegion", "PROVED (paperThetaHullScaled_zero)"),
    ("closed form reduction", "thetaScaledLog = scaledClosedFormR k -> statement", "PROVED conditional (scaledPaper312_of_closedForm)"),
    ("capsule average", "(1/n) Σ_j (j²-1) = sFactor(n)-1", "GREEN (shell_average_identity)"),
    ("j=1 capsule", "(1²-1)=0: automatic contribution", "PROVED"),
    ("unconditional equivalence", "ScaledPaper312Statement ↔ (sFactor-1)A <= V_paper", "GAP: needs analytic log identification + V_paper definition") ]

theorem scaledPaperRows_length : scaledPaperRows.length = 8 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScaledPaper312Actual.paperThetaHullScaled_zero
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScaledPaper312Actual.scaledPaper312_of_closedForm
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ScaledPaper312Actual.capsule_one_exponent_zero

end LeanFormal.IUT.XiFPaper.Mzk1ScaledPaper312Actual

end