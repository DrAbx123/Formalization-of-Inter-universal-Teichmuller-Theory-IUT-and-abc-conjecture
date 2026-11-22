import tmp.sheaf.iut4sec1.Iut4Sec1.Real.LogError
import tmp.sheaf.iut4sec1.Iut4Sec1.Combinatorics.RangeAverages
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1IUTIVSection1ConstantsActual — IUT IV §1 constant object

Real object built from the ported iut4-sec1 theorems: the nonarchimedean
log-error constants and the E1/E2 range averages of IUT IV §1.  The structure
stores the actual functions and their proved bounds (no Prop placeholder). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIVSection1ConstantsActual

open Iut4Sec1

/-- The IUT IV §1 elementary constant object. -/
structure IUTIVSection1Constants where
  logError : ℕ → ℕ → ℝ
  logError_eq : ∀ p e, logError p e = nonarchimedeanLogError p e
  logError_nonneg : ∀ p e, 2 < p → 0 < e → 0 ≤ logError p e
  logError_le_four : ∀ p e, p.Prime → 2 < p → 0 < e →
    logError p e ≤ 4 / (p : ℝ)
  averageSum : ∀ n : ℕ, 0 < n →
    (1 / (n : ℝ)) * ∑ m ∈ Finset.range n, (m + 1 : ℝ) =
      ((n : ℝ) + 1) / 2
  averageSqSum : ∀ n : ℕ, 0 < n →
    (1 / (n : ℝ)) * ∑ m ∈ Finset.range n, (m + 1 : ℝ) ^ 2 =
      ((2 * (n : ℝ) + 1) * ((n : ℝ) + 1)) / 6

/-- The canonical object from the ported IUT IV §1 theorems. -/
def iutIVSection1Constants : IUTIVSection1Constants where
  logError := nonarchimedeanLogError
  logError_eq := fun _ _ => rfl
  logError_nonneg := nonarchimedeanLogError_nonneg
  logError_le_four := nonarchimedeanLogError_le_four_div
  averageSum := average_range_sum
  averageSqSum := average_range_sq_sum

/-- Consumer: the explicit four-div-p error bound holds for the constant object. -/
theorem iutIVSection1_logError_le_four
    (C : IUTIVSection1Constants) (p e : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (he : 0 < e) : C.logError p e ≤ 4 / (p : ℝ) :=
  C.logError_le_four p e hp hp2 he

end LeanFormal.IUT.XiFPaper.Mzk1IUTIVSection1ConstantsActual

end
