/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # A881 hull: chain-two volume data (logMuPaper, arch, different)

Per-place paper-normalized data:
* logMuPaper = (1 + [p=2] - 1/e - r/n) log p;
* arch = log(sqrt 2 * pi);
* different = -order log p - torsion + arch, torsion = r/n.
Instances: p = 11 (e = 10, r = 1, n = 10) and p = 2. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1Chain2VolumeDataActual

def logMuPaper (p e r n : ℝ) : ℝ :=
  (1 + (if p = 2 then 1 else 0 : ℝ) - 1 / e - r / n) * Real.log p

def archTerm : ℝ := Real.log (Real.sqrt 2 * Real.pi)

theorem archTerm_eq_log : archTerm = Real.log 2 / 2 + Real.log Real.pi := by
  unfold archTerm
  rw [Real.log_mul (by positivity) Real.pi_ne_zero,
    Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

def torsionTerm (r n : ℝ) : ℝ := r / n

def differentTerm (order logp r n : ℝ) : ℝ :=
  -order * logp - torsionTerm r n + archTerm

/-- p = 11, e = 10, r = 1, n = 10: logMuPaper = (4/5) log 11. -/
theorem logMuPaper_p11 : logMuPaper 11 10 1 10 = (4 / 5) * Real.log 11 := by
  unfold logMuPaper
  have h : (1 + (if (11 : ℝ) = 2 then 1 else 0) - 1 / 10 - 1 / 10 : ℝ) = 4 / 5 := by
    norm_num
  rw [h]

theorem torsionTerm_p11 : torsionTerm 1 10 = 1 / 10 := by
  unfold torsionTerm
  norm_num

/-- p = 2, e = 2, r = 1, n = 2: logMuPaper = (3/2) log 2. -/
theorem logMuPaper_p2 : logMuPaper 2 2 1 2 = Real.log 2 := by
  unfold logMuPaper
  have h : (1 + (if (2 : ℝ) = 2 then 1 else 0) - 1 / 2 - 1 / 2 : ℝ) = 1 := by
    norm_num
  rw [h]
  ring

/-- different at p = 11, order 1: -log 11 - 1/10 + arch. -/
theorem differentTerm_p11_order1 :
    differentTerm 1 (Real.log 11) 1 10 = -Real.log 11 - 1 / 10 + archTerm := by
  unfold differentTerm torsionTerm
  norm_num

def chain2Rows : List (String × String × String) :=
  [ ("logMuPaper", "(1+[p=2]-1/e-r/n) log p", "DEF"),
    ("p=11,e=10,r=1,n=10", "logMuPaper = (4/5) log 11", "PROVED (logMuPaper_p11)"),
    ("p=2,e=2,r=1,n=2", "logMuPaper = log 2", "PROVED (logMuPaper_p2)"),
    ("arch", "log(sqrt 2 * pi) = log2/2 + log pi = 1.491303", "DEF + PROVED (archTerm_eq_log)"),
    ("torsion", "r/n", "DEF"),
    ("different", "-order log p - r/n + arch", "DEF"),
    ("p=11 order 1", "-log 11 - 1/10 + arch", "PROVED (differentTerm_p11_order1)") ]

theorem chain2Rows_length : chain2Rows.length = 7 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Chain2VolumeDataActual.archTerm_eq_log
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Chain2VolumeDataActual.logMuPaper_p11
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Chain2VolumeDataActual.logMuPaper_p2
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Chain2VolumeDataActual.differentTerm_p11_order1

end LeanFormal.IUT.XiFPaper.Mzk1Chain2VolumeDataActual

end
