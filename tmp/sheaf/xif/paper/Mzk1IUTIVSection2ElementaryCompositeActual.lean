import LeanFormal.IUT.IUTIV.Estimates.Section2
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1IUTIVSection2ElementaryCompositeActual — Prop 2.1 / Prop 1.6 composite

Genuine composite of the existing IUT IV §2 elementary estimates:
* two-sided theta bound eventually (Prop 2.1(ii));
* prime-counting bound (Prop 1.6, first form);
* nth-prime index bound (Prop 1.6, second form);
* log x <= x (Prop 2.1(i)).
No new paper input; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIVSection2ElementaryCompositeActual

open LeanFormal.IUT.IUTIV.Estimates

theorem iutIVSection2_elementary_composite :
    (∃ ξ : ℝ, 5 ≤ ξ ∧ ∀ x : ℝ, ξ ≤ x →
        2 / 3 * x ≤ Chebyshev.theta x ∧ Chebyshev.theta x ≤ 4 / 3 * x) ∧
      (∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η₀ ≤ η →
        (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4 * η / (3 * Real.log η)) ∧
      (∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ((n + 1 : ℕ) : ℝ) ≤
          4 * (Nat.nth Nat.Prime n : ℝ) /
            (3 * Real.log (Nat.nth Nat.Prime n : ℝ))) ∧
      (∀ x : ℝ, 1 ≤ x → Real.log x ≤ x) :=
  ⟨iutIVProp21ii_theta_two_sided_eventually,
   iutIVProp16_primeCounting_le_four_thirds_eventually,
   iutIVProp16_index_le_four_thirds_nthPrime,
   fun x hx => iutIVProp21i_log_le_self x hx⟩

end LeanFormal.IUT.XiFPaper.Mzk1IUTIVSection2ElementaryCompositeActual

end
