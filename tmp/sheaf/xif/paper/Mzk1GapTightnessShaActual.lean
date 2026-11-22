import tmp.sheaf.xif.paper.Mzk1ABCTwoEstimatesGapLimitShaActual
import Mathlib.Tactic

/-!
# shehdd A646 GapTightness calibration (Sha)

Calibration/tightness witnesses for the two estimate shapes:
* with epsilon > 0 slack, the epsilon-form does not force the pointwise bound:
  there are samples `h <= (1+eps)*L` with `L < h` (Gap1), and
  `v <= (1+eps)*w + hull + D` with `w+hull+D < v` (Gap2 uniform-D);
* only the limit/uniform hypotheses of
  `gap1_epsilon_iff_pointwise` / `gap2_uniform_iff_pointwise` recover the
  pointwise bounds; this calibrates exactly what the named gaps carry.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1GapTightnessShaActual

open LeanFormal.IUT.XiFPaper.Mzk1ABCTwoEstimatesGapLimitShaActual

/-- Gap1 tightness: epsilon-slack samples exist where the eps-form holds but the
pointwise bound fails. -/
theorem gap1_slack_calibration (epsilon : Real) (heps : 0 < epsilon) :
    ∃ h L : Real, 0 < L ∧ h ≤ (1 + epsilon) * L ∧ L < h := by
  refine ⟨(1 + epsilon / 2), 1, by norm_num, ?_, ?_⟩
  · nlinarith
  · linarith

/-- Gap2 tightness (uniform D): epsilon-slack samples exist where the eps-form
holds but the pointwise additive bound fails. -/
theorem gap2_slack_calibration (epsilon : Real) (heps : 0 < epsilon)
    (w hull D : Real) (hw : 0 < w) :
    ∃ v : Real, v ≤ (1 + epsilon) * w + hull + D ∧ w + hull + D < v := by
  refine ⟨(1 + epsilon / 2) * w + hull + D, ?_, ?_⟩
  · have hpos : 0 < (epsilon / 2) * w := mul_pos (by linarith) hw
    nlinarith
  · have hpos : 0 < (epsilon / 2) * w := mul_pos (by linarith) hw
    nlinarith

/-- The limit/uniform hypotheses are exactly what recovers the pointwise bound
(re-exported calibration pair from the GapLimit file). -/
theorem tightness_iff_pointwise_recovery {h L : Real} (hL : 0 < L) :
    (∀ ε : Real, 0 < ε → h ≤ (1 + ε) * L) ↔ h ≤ L :=
  gap1_epsilon_iff_pointwise hL

theorem tightness_volume_recovery {v w hull D : Real} (hw : 0 < w) :
    (∀ ε : Real, 0 < ε → v ≤ (1 + ε) * w + hull + D) ↔
      v ≤ w + hull + D :=
  gap2_uniform_iff_pointwise hw

structure TightnessRow where
  shape : String
  calibration : String
  status : String
  deriving Repr, DecidableEq

def tightnessRows : List TightnessRow :=
  [ ⟨"Gap1 eps-form", "gap1_slack_calibration: h=(1+eps/2), L=1", "GREEN"⟩
  , ⟨"Gap2 uniform-D eps-form", "gap2_slack_calibration: v=(1+eps/2)w+hull+D", "GREEN"⟩
  , ⟨"pointwise recovery", "gap1_epsilon_iff_pointwise / gap2_uniform_iff_pointwise", "GREEN"⟩
  , ⟨"scope", "calibration only; named gaps remain named", "INTEGRITY"⟩
  ]

theorem tightnessRows_length : tightnessRows.length = 4 := rfl

theorem tightnessRows_statuses_ok :
    tightnessRows.all (fun r => r.status ∈ ["GREEN", "INTEGRITY"]) = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1GapTightnessShaActual
