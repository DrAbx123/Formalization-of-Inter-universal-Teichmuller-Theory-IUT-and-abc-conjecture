import tmp.sheaf.xif.paper.Mzk1Lemma21dEvenActual
import tmp.sheaf.xif.paper.Mzk1Lemma21dOddActual
import Mathlib.Tactic

/-! # Mzk1Lemma21dAssemblyActual — [Mzk1] Lemma 2.1(d) ASSEMBLED (PROVED, both parities)

STEP 0 prior-art: corpus Lemma 2.1 lines 44-105; assembly over the GREEN+CITABLE
components Mzk1Lemma21dEvenActual (mzk1Lemma21_d_even) and Mzk1Lemma21dOddActual
(mzk1Lemma21_d_odd), themselves built from RatioEven/Odd/Dichotomy/Squared/Quarter,
Mzk1Lemma21RealActual/ImageActual and Mzk1Lemma22ProofActual (belyi22f0).

PAPER (d): (f(beta)+f0)/(f(alpha)+f0) >= C for all alpha in S\{infinity} with
f(alpha)+f0 != 0, where f0 = -min_alpha f(alpha).

THIS FILE proves the assembled lemma mzk1Lemma21_d (finite real form) by splitting on
the parity of n.  No fake: parity split is exhaustive; both branches are proved. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma21dAssemblyActual

open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RealActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22ProofActual

/-- [Mzk1] Lemma 2.1(d), finite real form, both parities. -/
theorem mzk1Lemma21_d {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (S : Finset ℝ) (β r C : ℝ) (hS : S.Nonempty)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (hr : r ∈ S) (hr0 : 0 < r) (hr1 : r < 1)
    (hbig : ∀ α ∈ S, α ≠ 0 → α ≠ 1 → α ≠ r → 1 < α)
    (hr_eq : r = (m : ℝ) / ((m + n : ℕ) : ℝ))
    (hC2 : 2 ≤ C) (hsep : ∀ α ∈ S, α ≠ 0 → C ≤ β / α) :
    ∀ α ∈ S, α ≠ 0 → α ≠ 1 →
      belyi21R m n α + belyi22f0 (m := m) (n := n) S hS ≠ 0 →
      C ≤ (belyi21R m n β + belyi22f0 (m := m) (n := n) S hS) /
          (belyi21R m n α + belyi22f0 (m := m) (n := n) S hS) := by
  by_cases hne : Even n
  · intro α hα hα0 hα1 hden
    exact LeanFormal.IUT.XiFPaper.Mzk1Lemma21dEvenActual.mzk1Lemma21_d_even
      hm hn hne S β r C hS h0 h1 hr hr0 hr1 hbig hC2 hsep α hα hα0 hα1
  · have hodd : Odd n := Nat.not_even_iff_odd.mp hne
    exact LeanFormal.IUT.XiFPaper.Mzk1Lemma21dOddActual.mzk1Lemma21_d_odd
      hm hn hodd S β r C hS h0 h1 hr hr0 hr1 hbig hr_eq hC2 hsep

#check mzk1Lemma21_d

end LeanFormal.IUT.XiFPaper.Mzk1Lemma21dAssemblyActual
end
