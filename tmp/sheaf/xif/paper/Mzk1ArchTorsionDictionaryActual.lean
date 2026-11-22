/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.Tactic

/-! # B10 hull support: archimedean and torsion dictionary terms

Paper dictionary terms:
* archimedean: `arch = log(sqrt 2 * pi) = log 2 / 2 + log pi` (positive);
* torsion: `torsion = r/n`, with `0 <= r <= n` giving `0 <= torsion <= 1`;
* different term: `diff = -order·log p - torsion + arch`.

These are the arch/torsion entries of the per-place deficit expansion; the
remaining B10 checks (exact q normalization `A = log q` vs `(1/(2l))log q` and
the global `Σ`) are abc's scope. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ArchTorsionDictionaryActual

def archConstant : ℝ := Real.log (Real.sqrt 2 * Real.pi)

theorem archConstant_eq : archConstant = Real.log 2 / 2 + Real.log Real.pi := by
  unfold archConstant
  rw [Real.log_mul (by positivity) Real.pi_ne_zero,
    Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

def torsionTerm (r n : ℝ) : ℝ := r / n

theorem torsionTerm_eq (r n : ℝ) : torsionTerm r n = r / n := rfl

theorem torsionTerm_nonneg {r n : ℝ} (hr : 0 ≤ r) (hn : 0 < n) :
    0 ≤ torsionTerm r n := by
  unfold torsionTerm
  positivity

theorem torsionTerm_le_one {r n : ℝ} (hn : 0 < n) (hrn : r ≤ n) :
    torsionTerm r n ≤ 1 := by
  unfold torsionTerm
  rw [div_le_one hn]
  exact hrn

/-- Paper per-place different/arch/torsion term. -/
def diffTerm (order logp r n : ℝ) : ℝ :=
  -order * logp - torsionTerm r n + archConstant

theorem diffTerm_eq (order logp r n : ℝ) :
    diffTerm order logp r n = -order * logp - r / n + archConstant := by
  unfold diffTerm torsionTerm
  ring

theorem diffTerm_ge (order logp r n : ℝ) (hrn : torsionTerm r n ≤ 1) :
    -order * logp - 1 + archConstant ≤ diffTerm order logp r n := by
  unfold diffTerm
  linarith

def archTorsionRows : List (String × String × String) :=
  [ ("arch constant", "arch = log(sqrt 2*pi) = log2/2 + log pi", "PROVED (archConstant_eq)"),
    ("torsion", "torsion = r/n", "DEF (torsionTerm)"),
    ("torsion range", "0 <= r, 0 < n => torsion >= 0; r <= n => torsion <= 1", "PROVED (torsionTerm_nonneg / torsionTerm_le_one)"),
    ("different term", "diff = -order·log p - r/n + arch", "PROVED (diffTerm_eq)"),
    ("diff lower", "diff >= -order·logp - 1 + arch when torsion <= 1", "PROVED (diffTerm_ge)"),
    ("B10 remaining", "q normalization A=log q vs (1/(2l))log q, and global sum / index dictionary", "abc scope") ]

theorem archTorsionRows_length : archTorsionRows.length = 6 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ArchTorsionDictionaryActual.archConstant_eq
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ArchTorsionDictionaryActual.torsionTerm_le_one
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ArchTorsionDictionaryActual.diffTerm_eq

end LeanFormal.IUT.XiFPaper.Mzk1ArchTorsionDictionaryActual

end