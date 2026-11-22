/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1HVLemmaActual
import Mathlib.Tactic

/-! # Mzk1HViiiAssemblyActual — assembling h_V property (iii) from (a)+(b)+(c) (A780)

ROUTES §9 / A779 verdict: property (iii) of the h_V lemma needs three inputs:
  (a) the scaled theta-volume difference is bounded by the per-place different/
      conductor sum (this is where the green per-place different bounds enter);
  (b) the local-global dictionary `Sum d_p log p = log d`, `Sum delta_p log p = log f`;
  (c) the archimedean contribution (a non-positive remainder or a separate constant).

This file fixes the assembled statement: `HVIIIInputs` packages (a)+(b)+(c), and
`hV_iii_assembled` derives `h_V(E/M) - h_V(E) <= (l/2)(log d + log f)`.
No axiom, no sorry, no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HViiiAssemblyActual

/-- Inputs (a)+(b)+(c) for property (iii) of the h_V lemma. -/
structure HVIIIInputs where
  /-- the scaling parameter `l`. -/
  l : Real
  /-- `log d` (finite discriminant part). -/
  logd : Real
  /-- `log f` (conductor part). -/
  logf : Real
  /-- the height difference `h_V(E/M) - h_V(E)`. -/
  hVdiff : Real
  /-- (a) per-place different/conductor sum. -/
  diffSum : Real
  /-- (a) per-place conductor sum. -/
  condSum : Real
  /-- (c) archimedean contribution (a non-positive remainder). -/
  arch : Real
  hl : 0 ≤ l
  /-- (a) the scaled theta-volume difference is bounded by the per-place sum. -/
  hDiff : hVdiff ≤ (l / 2) * (diffSum + condSum + arch)
  /-- (b) local-global dictionary for the different. -/
  hDictD : diffSum = logd
  /-- (b) local-global dictionary for the conductor. -/
  hDictF : condSum = logf
  /-- (c) the archimedean remainder is non-positive. -/
  hArch : arch ≤ 0

/-- **Property (iii), assembled**: (a)+(b)+(c) give `h_V(E/M) - h_V(E) <= (l/2)(log d + log f)`. -/
theorem hV_iii_assembled (I : HVIIIInputs) :
    I.hVdiff ≤ (I.l / 2) * (I.logd + I.logf) := by
  have h1 : I.diffSum + I.condSum + I.arch ≤ I.logd + I.logf := by
    rw [I.hDictD, I.hDictF]
    linarith [I.hArch]
  have hmul : (I.l / 2) * (I.diffSum + I.condSum + I.arch) ≤ (I.l / 2) * (I.logd + I.logf) :=
    mul_le_mul_of_nonneg_left h1 (by linarith [I.hl])
  linarith [I.hDiff]

/-- **With an explicit archimedean constant**: if the archimedean term is bounded by a
constant `A`, then `h_Vdiff <= (l/2)(log d + log f) + (l/2)A`. -/
theorem hV_iii_assembled_with_constant {l logd logf hVdiff diffSum condSum arch A : Real}
    (hl : 0 ≤ l) (hDiff : hVdiff ≤ (l / 2) * (diffSum + condSum + arch))
    (hDictD : diffSum = logd) (hDictF : condSum = logf) (hArch : arch ≤ A) :
    hVdiff ≤ (l / 2) * (logd + logf) + (l / 2) * A := by
  have h1 : diffSum + condSum + arch ≤ logd + logf + A := by
    rw [hDictD, hDictF]
    linarith
  have hmul : (l / 2) * (diffSum + condSum + arch) ≤ (l / 2) * (logd + logf + A) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have hsplit : (l / 2) * (logd + logf + A) = (l / 2) * (logd + logf) + (l / 2) * A := by
    ring
  linarith [hDiff, hmul, hsplit]

/-- Status rows. -/
def hvIiiRows : List (String × String) :=
  [ ("(a) scaled theta-volume difference <= per-place different/conductor sum",
     "INPUT — needs volume-difference identity + green per-place bounds"),
    ("(b) Sum d_p log p = log d", "INPUT — local-global discriminant dictionary"),
    ("(b) Sum delta_p log p = log f", "INPUT — local-global conductor dictionary"),
    ("(c) archimedean remainder <= 0 (or explicit constant)", "INPUT"),
    ("assembly (a)+(b)+(c) => (iii)", "PROVED (hV_iii_assembled)") ]

theorem hvIiiRows_length : hvIiiRows.length = 5 := rfl

#check hV_iii_assembled
#check hV_iii_assembled_with_constant
#check hvIiiRows_length

end LeanFormal.IUT.XiFPaper.Mzk1HViiiAssemblyActual
end
