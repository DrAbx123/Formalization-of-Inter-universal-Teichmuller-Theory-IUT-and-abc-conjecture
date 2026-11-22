/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Mzk1ArchBoundActual — (c) archimedean bound interface (A786/A790, qpilot)

Part (c) of the h_V property-(iii) assembly: the archimedean contribution.
The candidate constant is the standard IUT III Prop. 3.2(ii) type value
`m * log(sqrt 2 * pi)` for `m` archimedean components.

Proved here (pure real arithmetic):
* `log_sqrtTwo_pi_pos : 0 < log(sqrt 2 * pi)` (the candidate is positive);
* `archCandidate_nonneg`, `archCandidate_mono`;
* conditional interface `arch_le_of_candidate`: any archimedean term bounded by the
  candidate constant satisfies `arch ≤ m * log(sqrt 2 * pi)`; combined with
  `Mzk1HViiiAssemblyActual.hV_iii_assembled_with_constant` this gives the (iii) bound
  with explicit constant.

Still missing (documented in the rows): a *green proof* that the actual archimedean
hull Haar term of our S3137 carrier is bounded by this candidate (lana's
`componentVol_archLogShell_le_leastHull_le` is not compiled locally).

No axiom, no sorry, no `True` placeholder. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ArchBoundActual

/-- The standard archimedean constant `log(sqrt 2 * pi)`. -/
def archConstant : Real := Real.log (Real.sqrt 2 * Real.pi)

theorem log_sqrtTwo_pi_pos : 0 < archConstant := by
  unfold archConstant
  apply Real.log_pos
  nlinarith [Real.one_lt_sqrt_two, Real.pi_gt_three]

/-- The archimedean candidate for `m` components. -/
def archCandidate (m : Nat) : Real := (m : Real) * archConstant

theorem archCandidate_nonneg (m : Nat) : 0 ≤ archCandidate m := by
  unfold archCandidate
  exact mul_nonneg (Nat.cast_nonneg m) (le_of_lt log_sqrtTwo_pi_pos)

theorem archCandidate_mono {m n : Nat} (h : m ≤ n) :
    archCandidate m ≤ archCandidate n := by
  unfold archCandidate
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast h
  · exact le_of_lt log_sqrtTwo_pi_pos

/-- Conditional (c): any archimedean term bounded by the candidate is bounded by
`m * log(sqrt 2 * pi)`. -/
theorem arch_le_of_candidate {arch : Real} {m : Nat}
    (h : arch ≤ archCandidate m) : arch ≤ archCandidate m := h

/-- Combined form: if the archimedean remainder is bounded by `A = archCandidate m`,
the h_V (iii) bound becomes `hVdiff ≤ (l/2)(log d + log f) + (l/2) * m * log(sqrt 2 π)`. -/
theorem hV_iii_with_arch {l logd logf hVdiff diffSum condSum arch : Real} {m : Nat}
    (hl : 0 ≤ l) (hDiff : hVdiff ≤ (l / 2) * (diffSum + condSum + arch))
    (hDictD : diffSum = logd) (hDictF : condSum = logf)
    (hArch : arch ≤ archCandidate m) :
    hVdiff ≤ (l / 2) * (logd + logf) + (l / 2) * archCandidate m := by
  have h1 : diffSum + condSum + arch ≤ logd + logf + archCandidate m := by
    rw [hDictD, hDictF]
    linarith
  have hmul : (l / 2) * (diffSum + condSum + arch) ≤
      (l / 2) * (logd + logf + archCandidate m) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have hsplit : (l / 2) * (logd + logf + archCandidate m) =
      (l / 2) * (logd + logf) + (l / 2) * archCandidate m := by ring
  linarith [hDiff, hmul, hsplit]

def archRows : List (String × String) :=
  [ ("arch constant log(sqrt 2 * pi) > 0", "PROVED"),
    ("archCandidate m = m * log(sqrt 2 * pi), nonneg/mono", "PROVED"),
    ("(c) from arch ≤ candidate", "PROVED (conditional)"),
    ("h_V (iii) with explicit arch constant", "PROVED (conditional)"),
    ("actual archimedean hull term ≤ candidate", "MISSING (no local green hull arch bound)") ]

theorem archRows_length : archRows.length = 5 := rfl

#check log_sqrtTwo_pi_pos
#check hV_iii_with_arch
#check archRows_length

end LeanFormal.IUT.XiFPaper.Mzk1ArchBoundActual
end
