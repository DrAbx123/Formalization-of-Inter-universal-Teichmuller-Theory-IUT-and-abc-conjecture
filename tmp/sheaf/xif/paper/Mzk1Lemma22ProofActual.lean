import tmp.sheaf.xif.paper.Mzk1Lemma21RealActual
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-! # Mzk1Lemma22ProofActual — [Mzk1] Lemma 2.2 proof work (f0-normalization facts PROVED)

STEP 0 prior-art: corpus papers/motizuki_corpus/text/Noncritical Belyi Maps.txt Lemma 2.1
lines 44-64 and Lemma 2.2 lines 106-135; Mzk1Lemma21Actual (derivative/root dichotomy
PROVED), Mzk1Lemma21RealActual (zero/one values + monotonicity PROVED),
Mzk1Lemma21ImageActual (property (c) PROVED); Mathlib Finset inf'/min API reused.

PAPER (Lemma 2.1/2.2 proof device): f0 := -min_{alpha in S} f(alpha) with
f(x)=x^m(x-1)^n.  The paper replaces f by f + f0 in the induction step, then
rescale/renormalizes so that f(S) sits inside {0,1,infinity} and f(beta) is kept
away.  This file PROVES the f0-normalization facts needed by that step:
* the minimum is attained (finite S nonempty);
* f(alpha)+f0 >= 0 for all alpha in S (nonnegativity after shift);
* f(alpha)+f0 > 0 unless alpha attains the minimum (strict positivity off the min);
* the shifted values at 0 and 1 are exactly f0 (using m,n>=1).

HONEST: this is the f0-normalization part only.  The remaining Lemma 2.2 content
(induction on |S|, rational-coefficient descent, P1-morphism/unramifiedness) is
recorded in the row list with proved:=false. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22ProofActual

open Finset
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RealActual

variable {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)

/-- The shift constant f0 = -min_{alpha in S} f(alpha) (Lemma 2.1/2.2 normalization). -/
noncomputable def belyi22f0 (S : Finset ℝ) (hS : S.Nonempty) : ℝ :=
  -(S.inf' hS (fun x => belyi21R m n x))

/-- The minimum of f over S is attained (finite nonempty S). -/
theorem belyi22_min_attained (S : Finset ℝ) (hS : S.Nonempty) :
    ∃ v ∈ S, belyi21R m n v = S.inf' hS (fun x => belyi21R m n x) := by
  obtain ⟨v, hv, hveq⟩ := Finset.exists_mem_eq_inf' hS (fun x => belyi21R m n x)
  exact ⟨v, hv, hveq.symm⟩

/-- After the f0 shift, all values f(alpha)+f0 are nonnegative on S. -/
theorem belyi22_add_f0_nonneg (S : Finset ℝ) (hS : S.Nonempty) {α : ℝ} (hα : α ∈ S) :
    0 ≤ belyi21R m n α + belyi22f0 (m := m) (n := n) S hS := by
  unfold belyi22f0
  have hle : S.inf' hS (fun x => belyi21R m n x) ≤ belyi21R m n α :=
    Finset.inf'_le (fun x => belyi21R m n x) hα
  linarith

/-- Off the minimum, the shifted value is strictly positive. -/
theorem belyi22_add_f0_pos_of_not_min (S : Finset ℝ) (hS : S.Nonempty) {α : ℝ}
    (hα : α ∈ S)
    (hneq : belyi21R m n α ≠ S.inf' hS (fun x => belyi21R m n x)) :
    0 < belyi21R m n α + belyi22f0 (m := m) (n := n) S hS := by
  unfold belyi22f0
  have hle : S.inf' hS (fun x => belyi21R m n x) ≤ belyi21R m n α :=
    Finset.inf'_le (fun x => belyi21R m n x) hα
  have hlt : S.inf' hS (fun x => belyi21R m n x) < belyi21R m n α :=
    lt_of_le_of_ne hle (Ne.symm hneq)
  linarith

/-- The shifted values at 0 and 1 are exactly f0 (m,n >= 1). -/
theorem belyi22_shift_zero {m n : ℕ} (hm : 1 ≤ m) (S : Finset ℝ) (hS : S.Nonempty) :
    belyi21R m n 0 + belyi22f0 (m := m) (n := n) S hS = belyi22f0 (m := m) (n := n) S hS :=
  by rw [belyi21R_zero m n hm]; ring

theorem belyi22_shift_one {m n : ℕ} (hn : 1 ≤ n) (S : Finset ℝ) (hS : S.Nonempty) :
    belyi21R m n 1 + belyi22f0 (m := m) (n := n) S hS = belyi22f0 (m := m) (n := n) S hS :=
  by rw [belyi21R_one m n hn]; ring

/-- Remaining Lemma 2.2 obligations (data rows; not proved here). -/
structure Mzk1Lemma22ObligationRow where
  item : String
  status : String
  proved : Bool

def mzk1Lemma22Obligations : List Mzk1Lemma22ObligationRow :=
  [ ⟨"f0 normalization facts", "PROVED (this file): minimum attained, nonnegativity, strict positivity off min, shift at 0/1", true⟩,
    ⟨"induction on |S|", "PENDING: apply Lemma 2.1 to lambda*S, replace f by f+f0, iterate until |S|=3, compose", false⟩,
    ⟨"rational-coefficient descent", "PENDING: clear denominators / Q[x] construction", false⟩,
    ⟨"P1-morphism/unramifiedness language", "PENDING: Mathlib has RatFunc and unramified morphisms of schemes, but no Belyi-map interface; needs assembly", false⟩ ]

theorem mzk1Lemma22Obligations_length : mzk1Lemma22Obligations.length = 4 := rfl

#check belyi22_min_attained
#check belyi22_add_f0_nonneg
#check belyi22_add_f0_pos_of_not_min
#check belyi22_shift_zero
#check mzk1Lemma22Obligations_length

end LeanFormal.IUT.XiFPaper.Mzk1Lemma22ProofActual
end