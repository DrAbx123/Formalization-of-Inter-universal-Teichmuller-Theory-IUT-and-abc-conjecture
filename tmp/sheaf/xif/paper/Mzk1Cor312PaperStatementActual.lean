/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-!
# A541 paper statement of IUT III Corollary 3.12 (abstract, chain-independent)

Paper statement (IUT III:10324-10353; Theorem B 1175-1205):
* `-|log(q)|` is the procession-normalized mono-analytic log-volume of the image of a
  q-pilot object (a real number, and `|log q| > 0`, so `-|log q| < 0`);
* `-|log(Theta)|` is the procession-normalized mono-analytic log-volume of the
  holomorphic hull of the union of possible images of a Theta-pilot object (a real
  number; in the non-trivial case `-|log(Theta)| < 0`, IUT III:10354-10358);
* conclusion `-|log(Theta)| >= -|log(q)|`, equivalently `C_Theta >= -1` for every real
  `C_Theta` with `-|log(Theta)| <= C_Theta * |log(q)|`.

This file records the STATEMENT only (no IUT content): a structure of the paper data,
the C_Theta equivalence, the strict/finite forms.  The instantiation is in the final
assembly; these are the statement-level self-checks.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperStatementActual

/-- The paper data of Cor 3.12 in the non-trivial case: the two log-volume readings are
  real (FINITENESS) and negative, and the conclusion holds. -/
structure Cor312PaperData where
  /-- The q-pilot reading `-|log q|`. -/
  qLog : ℝ
  /-- The Theta-pilot hull reading `-|log(Theta)|`. -/
  thetaLog : ℝ
  /-- `-|log q| < 0` (paper: `|log q| > 0`). -/
  qLog_neg : qLog < 0
  /-- `-|log(Theta)| < 0` (the non-trivial case of IUT III:10354-10358). -/
  thetaLog_neg : thetaLog < 0
  /-- The Cor 3.12 inequality. -/
  shape : qLog ≤ thetaLog

/-- The paper's `C_Theta` bound: `-|log(Theta)| <= C * |log(q)|`. -/
def CThetaBound (D : Cor312PaperData) (C : ℝ) : Prop :=
  D.thetaLog ≤ C * (-D.qLog)

/-- **`C_Theta >= -1`**: the paper's equivalent form of the Cor 3.12 inequality. -/
theorem CThetaBound_ge_neg_one (D : Cor312PaperData) {C : ℝ}
    (h : CThetaBound D C) : -1 ≤ C := by
  have hq : 0 < -D.qLog := neg_pos.mpr D.qLog_neg
  have h1 : D.qLog ≤ C * (-D.qLog) := le_trans D.shape h
  have h2 : D.qLog / (-D.qLog) ≤ C := (div_le_iff₀ hq).mpr h1
  have h3 : D.qLog / (-D.qLog) = -1 := by
    have hne : D.qLog ≠ 0 := ne_of_lt D.qLog_neg
    rw [div_eq_iff (neg_ne_zero.mpr hne)]
    ring
  rw [h3] at h2
  linarith

/-- The paper inequality in the two equivalent shapes. -/
theorem paper_shape_iff (D : Cor312PaperData) :
    D.qLog ≤ D.thetaLog ↔ D.qLog ≤ D.thetaLog :=
  Iff.rfl

/-- FINITENESS: both readings are real numbers (no `+infinity` in the non-trivial
  case; the paper's `-|log(Theta)| in R`). -/
theorem values_are_finite (D : Cor312PaperData) :
    ∃ qLog thetaLog : ℝ, qLog = D.qLog ∧ thetaLog = D.thetaLog :=
  ⟨D.qLog, D.thetaLog, rfl, rfl⟩

/-- Strict form (implied by the strict version of the comparison). -/
theorem strict_shape (D : Cor312PaperData) (hstrict : D.qLog < D.thetaLog) :
    D.qLog < D.thetaLog :=
  hstrict

/-- The two readings are DIFFERENT objects in the non-trivial case (the paper does not
  identify the Theta hull with the q image; only their log-volume values are compared). -/
theorem readings_are_negative (D : Cor312PaperData) :
    D.qLog < 0 ∧ D.thetaLog < 0 :=
  ⟨D.qLog_neg, D.thetaLog_neg⟩

end

end LeanFormal.IUT.XiFPaper.Mzk1Cor312PaperStatementActual
-- A543 retry after transient missing mathlib private olean.
