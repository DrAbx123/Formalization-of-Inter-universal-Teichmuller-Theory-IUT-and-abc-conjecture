import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # S767: Theta hull log uses q[2u]; 2l normalization

For q[2u] = q[1u]^(1/(2l)), the minimal Theta hull log magnitude is
  |log q[2u]| = |log q[1u]|/(2l).
qPilot magnitude is |log q[1u]|.  Hence the signed Theta hull log is
  -qMag/(2l), the qPilot signed log is -qMag, and qPilotSigned <= thetaHullSigned
for qMag >= 0.  This is the paper comparison direction. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S767ThetaHull2lNormalizationActual

universe u

/-- Theta hull magnitude from the q[2u] root: qMag/(2l). -/
def thetaHullMagnitude (qMag : Real) (l : Nat) : Real :=
  qMag / (2 * (l : Real))

/-- qPilot signed log: -qMag, where qMag=|log q[1u]|. -/
def qPilotSignedLog (qMag : Real) : Real := -qMag

/-- Theta hull signed log: -qMag/(2l). -/
def thetaHullSignedLog (qMag : Real) (l : Nat) : Real :=
  -thetaHullMagnitude qMag l

/-- The root theta magnitude is at most the qPilot magnitude for qMag >= 0. -/
theorem thetaHullMagnitude_le_qMag (qMag : Real) (l : Nat) (hl : 0 < l)
    (hq : 0 <= qMag) :
    thetaHullMagnitude qMag l <= qMag := by
  unfold thetaHullMagnitude
  have hden : (0 : Real) < 2 * (l : Real) := by positivity
  have hge : (1 : Real) <= 2 * (l : Real) := by
    have : 1 <= 2 * l := by omega
    exact_mod_cast this
  rw [div_le_iff₀ hden]
  nlinarith [hq, hge, hden]

/-- Paper comparison direction: qPilotSigned <= thetaHullSigned. -/
theorem qPilotSigned_le_thetaHullSigned (qMag : Real) (l : Nat) (hl : 0 < l)
    (hq : 0 <= qMag) :
    qPilotSignedLog qMag <= thetaHullSignedLog qMag l := by
  unfold qPilotSignedLog thetaHullSignedLog thetaHullMagnitude
  have hden : (0 : Real) < 2 * (l : Real) := by positivity
  have hge : (1 : Real) <= 2 * (l : Real) := by
    have : 1 <= 2 * l := by omega
    exact_mod_cast this
  have hle : qMag / (2 * (l : Real)) <= qMag := by
    rw [div_le_iff₀ hden]
    nlinarith [hq, hge, hden]
  linarith

/-- Exact 2l factor: qMag = 2l * thetaHullMagnitude. -/
theorem qMag_eq_twoL_mul_thetaHullMagnitude (qMag : Real) (l : Nat) (hl : 0 < l) :
    qMag = (2 * (l : Real)) * thetaHullMagnitude qMag l := by
  unfold thetaHullMagnitude
  have hden : (0 : Real) ≠ 2 * (l : Real) := by positivity
  field_simp [hden]

end LeanFormal.IUT.XiFPaper.S767ThetaHull2lNormalizationActual

end
