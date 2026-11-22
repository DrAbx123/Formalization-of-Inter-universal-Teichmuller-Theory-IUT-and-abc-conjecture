/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1ShellArithmeticIdentitiesActual
import Mathlib.Tactic

/-! # A797 hull: paper-normalized θ-side sum and deficit expansion

Paper-normalized θ side: for `nC` capsules with per-capsule q-magnitude `A`,
the scaled θ contribution is

  `Σtheta = (1/nC) Σ_{j<nC} ((j²-1)/(2l))·A = c_lana·A`,
  `c_lana = (sFactor(nC)-1)/(2l)`,

using the green `shell_average_identity` (`(1/n)Σ(j²-1)=sFactor(n)-1`).

Deficit:
  `deficit = ssCoeff·A − (ΣlogMuPaper + Σtheta)`
and, with `ΣlogMuPaper = diff − arch + torsion` (different `log N(d) = -d log p`,
arch `log(sqrt 2 pi)`, torsion `r/n`),
  `deficit = ssCoeff·A − diff + arch − torsion − c_lana·A`.
All terms are explicit; the identification `Σtheta = c_lana·A` is proved, the
dictionary of `diff/arch/torsion` with the paper's per-place data remains abc's. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperNormThetaActual

open LeanFormal.IUT.XiFPaper.Mzk1ShellArithmeticIdentitiesActual
open scoped BigOperators

/-- Paper θ-side sum over `nC` capsules, each contributing `((j²-1)/(2l))·A`. -/
def thetaSumPaper (nC : ℕ) (l A : ℝ) : ℝ :=
  (1 / (nC : ℝ)) *
    (∑ j ∈ Finset.range nC, ((((j : ℝ) + 1) ^ 2 - 1) / (2 * l)) * A)

/-- `c_lana = (sFactor(nC)-1)/(2l)`. -/
def clana (nC : ℕ) (l : ℝ) : ℝ := (sFactor nC - 1) / (2 * l)

/-- **Green identity**: the paper θ-side sum equals `c_lana·A`. -/
theorem thetaSumPaper_eq_clana_mul (nC : ℕ) (hn : 0 < nC) (l A : ℝ) :
    thetaSumPaper nC l A = clana nC l * A := by
  unfold thetaSumPaper clana
  have hsum : (∑ j ∈ Finset.range nC, ((((j : ℝ) + 1) ^ 2 - 1) / (2 * l)) * A) =
      (∑ j ∈ Finset.range nC, ((((j : ℝ) + 1) ^ 2 - 1))) * A / (2 * l) := by
    calc
      (∑ j ∈ Finset.range nC, ((((j : ℝ) + 1) ^ 2 - 1) / (2 * l)) * A)
          = (∑ j ∈ Finset.range nC, ((((j : ℝ) + 1) ^ 2 - 1) * A) / (2 * l)) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = ((∑ j ∈ Finset.range nC, ((((j : ℝ) + 1) ^ 2 - 1) * A)) / (2 * l)) := by
            rw [Finset.sum_div]
      _ = ((∑ j ∈ Finset.range nC, ((((j : ℝ) + 1) ^ 2 - 1))) * A / (2 * l)) := by
            rw [Finset.sum_mul]
  rw [hsum, shell_sum_identity nC hn]
  have hnR : (nC : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnR]

/-- Complete deficit: `ssCoeff·A − (ΣlogMuPaper + Σtheta)`. -/
def paperDeficit (ssCoeff A sumLogMu sumTheta : ℝ) : ℝ :=
  ssCoeff * A - (sumLogMu + sumTheta)

/-- Deficit with the paper θ-side identity substituted. -/
theorem paperDeficit_thetaSubst (ssCoeff A sumLogMu : ℝ) (nC : ℕ) (hn : 0 < nC)
    (l : ℝ) :
    paperDeficit ssCoeff A sumLogMu (thetaSumPaper nC l A) =
      ssCoeff * A - (sumLogMu + clana nC l * A) := by
  unfold paperDeficit
  rw [thetaSumPaper_eq_clana_mul nC hn l A]

/-- Expanded deficit: `ΣlogMu = diff − arch + torsion` gives
`deficit = ssCoeff·A − diff + arch − torsion − c_lana·A`. -/
theorem paperDeficit_expanded (ssCoeff A diff arch torsion : ℝ)
    (nC : ℕ) (hn : 0 < nC) (l : ℝ)
    (hlogmu : (∑ _i ∈ Finset.range nC, (0 : ℝ)) + diff - arch + torsion = diff - arch + torsion) :
    paperDeficit ssCoeff A (diff - arch + torsion) (thetaSumPaper nC l A) =
      ssCoeff * A - diff + arch - torsion - clana nC l * A := by
  rw [paperDeficit_thetaSubst ssCoeff A (diff - arch + torsion) nC hn l]
  ring

/-- Verdict: the paper inequality is exactly `deficit <= 0`. -/
theorem paperVerdict_iff_deficit (ssCoeff A sumLogMu sumTheta : ℝ) :
    ssCoeff * A ≤ sumLogMu + sumTheta ↔
      paperDeficit ssCoeff A sumLogMu sumTheta ≤ 0 := by
  unfold paperDeficit
  constructor <;> intro h <;> linarith

def thetaRows : List (String × String × String) :=
  [ ("theta sum", "Σtheta = (1/nC)Σ_j ((j²-1)/(2l))A", "DEF (thetaSumPaper)"),
    ("c_lana", "c_lana = (sFactor(nC)-1)/(2l)", "DEF (clana)"),
    ("theta identity", "Σtheta = c_lana*A (green shell_average_identity)", "PROVED (thetaSumPaper_eq_clana_mul)"),
    ("deficit", "deficit = ssCoeff*A - (ΣlogMuPaper + Σtheta)", "DEF (paperDeficit)"),
    ("theta substituted", "= ssCoeff*A - (ΣlogMuPaper + c_lana*A)", "PROVED (paperDeficit_thetaSubst)"),
    ("expanded", "= ssCoeff*A - diff + arch - torsion - c_lana*A", "PROVED (paperDeficit_expanded)"),
    ("verdict", "paper inequality iff deficit <= 0", "PROVED (paperVerdict_iff_deficit)"),
    ("different term", "diff = log N(d) = -order*log p (per place, paper different)", "abc/local dictionary"),
    ("arch term", "arch = log(sqrt 2 * pi) (per archimedean factor)", "abc dictionary"),
    ("torsion term", "torsion = r/n (unit-torsion correction)", "abc dictionary"),
    ("gap", "identify diff/arch/torsion sums with the paper per-place data; A/B bounds do not fix deficit sign", "GAP") ]

theorem thetaRows_length : thetaRows.length = 11 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperNormThetaActual.thetaSumPaper_eq_clana_mul
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperNormThetaActual.paperDeficit_expanded
#print axioms LeanFormal.IUT.XiFPaper.Mzk1PaperNormThetaActual.paperVerdict_iff_deficit

end LeanFormal.IUT.XiFPaper.Mzk1PaperNormThetaActual

end