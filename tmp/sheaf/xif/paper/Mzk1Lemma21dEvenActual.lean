import tmp.sheaf.xif.paper.Mzk1Lemma21RatioEvenActual
import tmp.sheaf.xif.paper.Mzk1Lemma21RatioOddActual
import tmp.sheaf.xif.paper.Mzk1Lemma21RatioDichotomyActual
import tmp.sheaf.xif.paper.Mzk1Lemma21RatioSquaredActual
import tmp.sheaf.xif.paper.Mzk1Lemma21RatioQuarterActual
import Mathlib.Tactic

/-! # Mzk1Lemma21dEvenActual — [Mzk1] Lemma 2.1(d), n-even case ASSEMBLED (PROVED)

STEP 0 prior-art: corpus Lemma 2.1 lines 44-105; components all GREEN+CITABLE:
Mzk1Lemma21RatioEvenActual (f0=0 for n even; alpha>1 and alpha=r ratios),
Mzk1Lemma21RatioOddActual, Mzk1Lemma21RatioDichotomyActual, Mzk1Lemma21RatioSquaredActual,
Mzk1Lemma21RatioQuarterActual; Mzk1Lemma22ProofActual (belyi22f0).

THIS FILE assembles the n-even case of (d) into one theorem mzk1Lemma21_d_even:
under the Lemma 2.1 point conditions and condition (iv), for every alpha in S with
alpha != 0,1 the ratio (f(beta)+f0)/(f(alpha)+f0) >= C (with f0 = 0 for n even).
The n-odd case is assembled separately (Mzk1Lemma21dOddActual). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma21dEvenActual

open Finset
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RealActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22ProofActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RatioEvenActual

/-- n-even case of Lemma 2.1(d) (finite real form), assembled. -/
theorem mzk1Lemma21_d_even {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hne : Even n)
    (S : Finset ℝ) (β r C : ℝ) (hS : S.Nonempty)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (hr : r ∈ S) (hr0 : 0 < r) (hr1 : r < 1)
    (hbig : ∀ α ∈ S, α ≠ 0 → α ≠ 1 → α ≠ r → 1 < α)
    (hC2 : 2 ≤ C) (hsep : ∀ α ∈ S, α ≠ 0 → C ≤ β / α) :
    ∀ α ∈ S, α ≠ 0 → α ≠ 1 →
      C ≤ (belyi21R m n β + belyi22f0 (m := m) (n := n) S hS) /
          (belyi21R m n α + belyi22f0 (m := m) (n := n) S hS) := by
  have hC1 : (1 : ℝ) ≤ C := le_trans (by norm_num) hC2
  have hnonneg : ∀ α ∈ S, 0 ≤ belyi21R m n α := by
    intro α hα
    by_cases hα0 : α = 0
    · subst hα0; rw [belyi21R_zero m n hm]
    by_cases hα1 : α = 1
    · subst hα1; rw [belyi21R_one m n hn]
    by_cases hαr : α = r
    · subst hαr
      exact belyi21R_nonneg_on_unit (m := m) (n := n) hne (le_of_lt hr0) (le_of_lt hr1)
    · have hαgt : 1 < α := hbig α hα hα0 hα1 hαr
      exact le_of_lt (belyi21R_pos_of_one_lt (m := m) (n := n) hαgt)
  have hmin0 : S.inf' hS (fun x => belyi21R m n x) = 0 := by
    have hle : S.inf' hS (fun x => belyi21R m n x) ≤ 0 := by
      have h := Finset.inf'_le (s := S) (f := fun x => belyi21R m n x) h0
      rwa [belyi21R_zero m n hm] at h
    have hge : 0 ≤ S.inf' hS (fun x => belyi21R m n x) :=
      Finset.le_inf' hS (fun x => belyi21R m n x) (fun α hα => hnonneg α hα)
    exact le_antisymm hle hge
  have hf0 : belyi22f0 (m := m) (n := n) S hS = 0 := by
    unfold belyi22f0
    rw [hmin0]
    ring
  have hβC : C ≤ β := by
    have h := hsep 1 h1 (by norm_num : (1 : ℝ) ≠ 0)
    simpa using h
  have hβ2 : 2 ≤ β := le_trans hC2 hβC
  intro α hα hα0 hα1
  rw [hf0]
  simp only [add_zero]
  by_cases hαr : α = r
  · subst hαr
    exact belyi21R_div_ge_of_eq_r hm hn hne hr0 hr1 hC1 hβC hβ2
  · have hαgt : 1 < α := hbig α hα hα0 hα1 hαr
    have hαpos : 0 < α := by linarith
    have hCα : C * α ≤ β := by
      have h := hsep α hα hα0
      have := (le_div_iff₀ hαpos).mp h
      linarith
    have hαβ : α < β := by nlinarith
    exact belyi21R_div_ge_of_one_lt_sep hm hn hαgt hαβ hC1 (hsep α hα hα0)

#check mzk1Lemma21_d_even

end LeanFormal.IUT.XiFPaper.Mzk1Lemma21dEvenActual
end
