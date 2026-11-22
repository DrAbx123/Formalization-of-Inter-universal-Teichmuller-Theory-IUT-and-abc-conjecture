import tmp.sheaf.xif.paper.Mzk1GChoiceAvoidActual
import tmp.sheaf.xif.paper.Mzk1Lemma21Actual
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic

/-! # Mzk1GChoiceUnramifiedActual — unramifiedness for the g-choice step (scaled Lemma 2.1(b))

STEP 0 prior-art: resume priority (Lead).  Reuse: Mzk1Lemma21Actual (belyi21_derivative,
belyi21_derivative_root PROVED), Mzk1GChoiceAvoidActual (gPoly_eval etc.), Mzk1GChoiceDegreeActual,
Mzk1Lemma22StatementShapeActual.  No fake.  Proof: g'(x) = lambda * f'(lambda x); root
dichotomy gives lambda x in {0,1,r}; in each case g(x) equals g at a point of S, so it
lies in the image; contradiction with the unramifiedness hypothesis. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GChoiceUnramifiedActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21Actual

theorem lam_ne_zero' (D : Mzk1ScaleData) : D.lam ≠ 0 := by
  intro h
  have := D.hlam_alpha2
  rw [h, zero_mul] at this
  norm_num at this

theorem gPoly_derivative_eval (D : Mzk1ScaleData) (x : ℚ) :
    (gPoly D).derivative.eval x =
      D.lam * (derivative (belyi21 D.m D.n)).eval (D.lam * x) := by
  unfold gPoly
  rw [derivative_add, derivative_C, add_zero]
  have hB : ((X : ℚ[X]) ^ D.m * ((X : ℚ[X]) - 1) ^ D.n) = belyi21 D.m D.n := rfl
  rw [hB, derivative_comp, derivative_C_mul_X]
  simp [Polynomial.eval_mul, Polynomial.eval_comp]

theorem gPoly_derivative_zero_cases (D : Mzk1ScaleData) {x : ℚ}
    (h : (gPoly D).derivative.eval x = 0) :
    D.lam * x = 0 ∨ D.lam * x = 1 ∨
      ((D.m + D.n : ℕ) : ℚ) * (D.lam * x) = (D.m : ℚ) := by
  rw [gPoly_derivative_eval] at h
  have hlam : D.lam ≠ 0 := lam_ne_zero' D
  have hB0 : (derivative (belyi21 D.m D.n)).eval (D.lam * x) = 0 := by
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hlam
    · exact h1
  have hz : (Polynomial.aeval (((D.lam * x : ℚ) : ℂ))) (derivative (belyi21 D.m D.n)) = 0 := by
    have hcast : ((D.lam * x : ℚ) : ℂ) = algebraMap ℚ ℂ (D.lam * x) := rfl
    rw [hcast, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
    rw [hB0]
    simp
  rcases belyi21_derivative_root D.hm D.hn hz with h0 | h1 | hmn
  · left
    exact_mod_cast h0
  · right; left
    exact_mod_cast h1
  · right; right
    exact_mod_cast hmn

theorem fq_zero (D : Mzk1ScaleData) : fq D.m D.n 0 = 0 := by
  unfold fq
  rw [zero_pow (Nat.ne_of_gt (Nat.zero_lt_one.trans_le D.hm))]
  ring

theorem fq_one (D : Mzk1ScaleData) : fq D.m D.n 1 = 0 := by
  unfold fq
  rw [show (1 : ℚ) - 1 = 0 by ring,
    zero_pow (Nat.ne_of_gt (Nat.zero_lt_one.trans_le D.hn))]
  ring

theorem lam_mul_alpha1 (D : Mzk1ScaleData) : D.lam * D.alpha1 = D.r := by
  rw [D.lam_eq, D.r_eq, div_eq_inv_mul]

/-- Unramifiedness of the g-choice map over the complement of its image. -/
theorem gChoice_unramified (D : Mzk1ScaleData) (H : Lemma22Hypotheses D.S D.beta) :
    UnramifiedOver (polyMorphism (gPoly D) (gPoly_natDegree_pos D))
      {p | p ∉ (↑(D.S.image (polyMapPoints (gPoly D))) : Set (P1Point ℚ))}
      (polyUnramifiedAt (gPoly D)) := by
  obtain ⟨h0S, hInfS, hpos, hβnotin, hsep'⟩ := H
  intro p hp
  cases p with
  | none =>
      have hmem : (polyMapPoints (gPoly D) P1Point.infty) ∈
          (↑(D.S.image (polyMapPoints (gPoly D))) : Set (P1Point ℚ)) := by
        apply Finset.mem_image.mpr
        exact ⟨P1Point.infty, hInfS, rfl⟩
      have hmem' : (polyMorphism (gPoly D) (gPoly_natDegree_pos D)).mapPoints P1Point.infty ∈
          (↑(D.S.image (polyMapPoints (gPoly D))) : Set (P1Point ℚ)) := hmem
      exact (hp hmem').elim
  | some x =>
      by_contra hder
      have hder0 : (gPoly D).derivative.eval x = 0 := by
        simpa [polyUnramifiedAt] using not_not.mp hder
      have hlimage : ∀ y : ℚ, P1Point.ofFinite y ∈ D.S → (gPoly D).eval x = (gPoly D).eval y →
          (polyMapPoints (gPoly D) (P1Point.ofFinite x)) ∈
            (↑(D.S.image (polyMapPoints (gPoly D))) : Set (P1Point ℚ)) := by
        intro y hyS hy
        apply Finset.mem_image.mpr
        refine ⟨P1Point.ofFinite y, hyS, ?_⟩
        show some ((gPoly D).eval y) = some ((gPoly D).eval x)
        rw [hy]
      rcases gPoly_derivative_zero_cases D hder0 with h0 | h1 | hr
      · have hval : (gPoly D).eval x = (gPoly D).eval 0 := by
          rw [gPoly_eval, h0, gPoly_eval_zero, fq_zero D]
          ring
        exact hp (hlimage 0 h0S hval)
      · have hval : (gPoly D).eval x = (gPoly D).eval D.alpha2 := by
          rw [gPoly_eval, h1, gPoly_eval, D.hlam_alpha2, fq_one D]
        exact hp (hlimage D.alpha2 D.halpha2S hval)
      · have hlamxr : D.lam * x = D.r := by
          have hN : ((D.m + D.n : ℕ) : ℝ) ≠ 0 := by
            apply ne_of_gt
            have hpos : (0 : ℕ) < D.m + D.n :=
              Nat.add_pos_left (Nat.zero_lt_one.trans_le D.hm) D.n
            exact_mod_cast hpos
          have hcast : ((D.m + D.n : ℕ) : ℝ) * (((D.lam * x : ℚ)) : ℝ) = (D.m : ℝ) := by
            exact_mod_cast hr
          have h1 : (((D.lam * x : ℚ)) : ℝ) = (D.m : ℝ) / ((D.m + D.n : ℕ) : ℝ) := by
            rw [eq_div_iff hN, mul_comm]
            exact hcast
          have h2 : (((D.lam * x : ℚ)) : ℝ) = ((D.r : ℚ) : ℝ) := by
            rw [h1]
            exact D.hr_eq.symm
          exact Rat.cast_injective h2
        have hval : (gPoly D).eval x = (gPoly D).eval D.alpha1 := by
          rw [gPoly_eval, hlamxr, gPoly_eval, lam_mul_alpha1 D]
        exact hp (hlimage D.alpha1 D.halpha1S hval)

#check gChoice_unramified

end LeanFormal.IUT.XiFPaper.Mzk1GChoiceUnramifiedActual
end

-- touch 18:52 (force fresh olean)
