import tmp.sheaf.xif.paper.Mzk1Lemma22GChoiceDataActual
import tmp.sheaf.xif.paper.Mzk1Lemma21dAssemblyActual
import Mathlib.Tactic

/-! # Mzk1Lemma22GChoiceConstructActual — g-choice construction, consumer side (scale data -> Lemma 2.1)

STEP 0 prior-art: corpus Lemma 2.2 lines 106-135 (apply Lemma 2.1 to lambda*S; f+f0 gives
the step); Mzk1Lemma21dAssemblyActual (mzk1Lemma21_d PROVED); Mzk1Lemma22GChoiceDataActual
(packaging PROVED/CITABLE); Mzk1GChoiceScaleActual owned by stepxi (lambda/scaling family;
interface sent: scaleP/scaleS/two-smallest/memberships/scale_real_hypotheses).  This file
defines the consumer-side scale data and discharges the Lemma 2.1(d) conclusion on the
scaled set; the rational polynomial g = X^m (X-1)^n + f0q and the card/avoids/unramified
proofs are the next batch (rows).  No fake. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21RealActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22ProofActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21dAssemblyActual

/-- Consumer-side scale data: the output of stepxi's Mzk1GChoiceScaleActual, packaged with
the exact hypotheses of mzk1Lemma21_d on the scaled real set. -/
structure Mzk1ScaleData where
  S : Finset (P1Point ℚ)
  beta : P1Point ℚ
  b : ℚ
  beta_eq : beta = P1Point.ofFinite b
  alpha1 : ℚ
  alpha2 : ℚ
  lam : ℚ
  lam_eq : lam = alpha2⁻¹
  r : ℚ
  r_eq : r = alpha1 / alpha2
  scaledRealS : Finset ℝ
  scaledRatS : Finset ℚ
  scaledRealS_eq : scaledRealS = scaledRatS.image (fun q : ℚ => (q : ℝ))
  m : ℕ
  n : ℕ
  hm : 1 ≤ m
  hn : 1 ≤ n
  hSne : scaledRealS.Nonempty
  h0 : (0 : ℝ) ∈ scaledRealS
  h1 : (1 : ℝ) ∈ scaledRealS
  hr : ((r : ℚ) : ℝ) ∈ scaledRealS
  hr0 : 0 < ((r : ℚ) : ℝ)
  hr1 : ((r : ℚ) : ℝ) < 1
  hr_eq : ((r : ℚ) : ℝ) = (m : ℝ) / ((m + n : ℕ) : ℝ)
  hbig : ∀ x ∈ scaledRealS, x ≠ 0 → x ≠ 1 → x ≠ ((r : ℚ) : ℝ) → 1 < x
  realBeta : ℝ
  realBeta_eq : realBeta = ((lam * b : ℚ) : ℝ)
  hsep : ∀ x ∈ scaledRealS, x ≠ 0 → 2 ≤ realBeta / x
  hRatSne : scaledRatS.Nonempty
  halpha1S : P1Point.ofFinite alpha1 ∈ S
  halpha2S : P1Point.ofFinite alpha2 ∈ S
  halpha2_ne : alpha2 ≠ 0
  hlam_alpha2 : lam * alpha2 = 1
  mem_scaledRealS_of_mem : ∀ p ∈ S, p ≠ P1Point.infty → ∀ x : ℚ, p = P1Point.ofFinite x → 0 < x →
    ((lam * x : ℚ) : ℝ) ∈ scaledRealS
  hn_even : Even n
  lam_pos : 0 < lam
  zero_mem_scaledRatS : (0 : ℚ) ∈ scaledRatS
  scaledRatS_nonneg : ∀ q ∈ scaledRatS, 0 ≤ q
  halpha1_pos : 0 < alpha1
  halpha2_pos : 0 < alpha2
  partition : ∀ p ∈ S, p ≠ P1Point.ofFinite (0 : ℚ) → p ≠ P1Point.infty →
    p = P1Point.ofFinite alpha1 ∨ p = P1Point.ofFinite alpha2 ∨
      (∃ x : ℚ, p = P1Point.ofFinite x ∧ alpha2 < x)

/-- The rational polynomial f = x^m (x-1)^n evaluated in Q. -/
def fq (m n : ℕ) (x : ℚ) : ℚ := x ^ m * (x - 1) ^ n

/-- The rational shift f0 = -min over the scaled rational set. -/
def f0q (D : Mzk1ScaleData) : ℚ :=
  -(D.scaledRatS.inf' D.hRatSne (fun x => fq D.m D.n x))

/-- Lemma 2.1(d) on the scaled set, with C = 2 (consumer side). -/
theorem scale_lemma21_d (D : Mzk1ScaleData) :
    ∀ α ∈ D.scaledRealS, α ≠ 0 → α ≠ 1 →
      belyi21R D.m D.n α + belyi22f0 (m := D.m) (n := D.n) D.scaledRealS D.hSne ≠ 0 →
      2 ≤ (belyi21R D.m D.n D.realBeta +
            belyi22f0 (m := D.m) (n := D.n) D.scaledRealS D.hSne) /
          (belyi21R D.m D.n α + belyi22f0 (m := D.m) (n := D.n) D.scaledRealS D.hSne) :=
  mzk1Lemma21_d D.hm D.hn D.scaledRealS D.realBeta ((D.r : ℚ) : ℝ) 2 D.hSne
    D.h0 D.h1 D.hr D.hr0 D.hr1 D.hbig D.hr_eq (by norm_num) D.hsep

/-- Obligation rows for the remaining construction (next batches). -/
structure Mzk1GChoiceConstructRow where
  item : String
  status : String
  proved : Bool

def mzk1GChoiceConstructRows : List Mzk1GChoiceConstructRow :=
  [ ⟨"consumer scale data + Lemma 2.1(d) on scaled set (C=2)", "PROVED (this file)", true⟩,
    ⟨"coercion (f0q : R) = belyi22f0 scaledRealS (min commutes with coercion)", "PENDING (next batch)", false⟩,
    ⟨"polynomial g = X^m (X-1)^n + C f0q in Q[X], nonconstant (natDegree >= 2)", "PENDING", false⟩,
    ⟨"card collapse: g(0) = g(alpha2) = f0 (via lam*alpha2 = 1, f(0)=f(1)=0)", "PENDING", false⟩,
    ⟨"avoids: g(beta) notin image via scaled Lemma 2.1(c)", "PENDING", false⟩,
    ⟨"unramified: g'(x) != 0 off image via scaled Lemma 2.1(b) root dichotomy", "PENDING", false⟩ ]

theorem mzk1GChoiceConstructRows_length : mzk1GChoiceConstructRows.length = 6 := rfl


/-- Pointwise coercion: fq over Q coerces to the real belyi function. -/
theorem fq_coe (m n : ℕ) (x : ℚ) :
    ((fq m n x : ℚ) : ℝ) = belyi21R m n (x : ℝ) := by
  unfold fq belyi21R
  push_cast
  ring

/-- The rational minimum coerces to the real minimum: (f0q : R) = belyi22f0 scaledRealS. -/
theorem f0q_coe (D : Mzk1ScaleData) :
    ((f0q D : ℚ) : ℝ) =
      belyi22f0 (m := D.m) (n := D.n) D.scaledRealS D.hSne := by
  have hmem : ∀ x ∈ D.scaledRealS, ∃ q ∈ D.scaledRatS, (q : ℝ) = x := by
    intro x hx
    rw [D.scaledRealS_eq] at hx
    obtain ⟨q, hq, hqx⟩ := Finset.mem_image.mp hx
    exact ⟨q, hq, hqx⟩
  have hle : ((D.scaledRatS.inf' D.hRatSne (fun x => fq D.m D.n x) : ℚ) : ℝ) ≤
      D.scaledRealS.inf' D.hSne (fun x => belyi21R D.m D.n x) := by
    apply Finset.le_inf'
    intro x hx
    obtain ⟨q, hq, hqx⟩ := hmem x hx
    have hinf : D.scaledRatS.inf' D.hRatSne (fun x => fq D.m D.n x) ≤ fq D.m D.n q :=
      Finset.inf'_le (fun x => fq D.m D.n x) hq
    rw [← hqx]
    calc ((D.scaledRatS.inf' D.hRatSne (fun x => fq D.m D.n x) : ℚ) : ℝ)
        ≤ ((fq D.m D.n q : ℚ) : ℝ) := by exact_mod_cast hinf
      _ = belyi21R D.m D.n (q : ℝ) := fq_coe D.m D.n q
  have hge : D.scaledRealS.inf' D.hSne (fun x => belyi21R D.m D.n x) ≤
      ((D.scaledRatS.inf' D.hRatSne (fun x => fq D.m D.n x) : ℚ) : ℝ) := by
    obtain ⟨q, hq, hqeq⟩ := Finset.exists_mem_eq_inf' D.hRatSne (fun x => fq D.m D.n x)
    have hqR : (q : ℝ) ∈ D.scaledRealS := by
      rw [D.scaledRealS_eq]
      exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
    have h := Finset.inf'_le (s := D.scaledRealS) (f := fun x => belyi21R D.m D.n x) hqR
    rw [show ((D.scaledRatS.inf' D.hRatSne (fun x => fq D.m D.n x) : ℚ) : ℝ)
        = belyi21R D.m D.n (q : ℝ) from by
          rw [← fq_coe D.m D.n q, hqeq]]
    exact h
  have heq : ((D.scaledRatS.inf' D.hRatSne (fun x => fq D.m D.n x) : ℚ) : ℝ)
      = D.scaledRealS.inf' D.hSne (fun x => belyi21R D.m D.n x) := le_antisymm hle hge
  unfold f0q belyi22f0
  push_cast
  rw [heq]


/-- The rational polynomial g = f(lambda * x) + f0q defining the step, where
f(x) = x^m (x-1)^n and f0q is the rational shift. -/
def gPoly (D : Mzk1ScaleData) : ℚ[X] :=
  (((X : ℚ[X]) ^ D.m * ((X : ℚ[X]) - 1) ^ D.n).comp (C D.lam * X)) + C (f0q D)

/-- Evaluation formula for gPoly. -/
theorem gPoly_eval (D : Mzk1ScaleData) (x : ℚ) :
    (gPoly D).eval x = fq D.m D.n (D.lam * x) + f0q D := by
  unfold gPoly fq
  simp [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

/-- g(0) = f0q (m >= 1). -/
theorem gPoly_eval_zero (D : Mzk1ScaleData) :
    (gPoly D).eval 0 = f0q D := by
  rw [gPoly_eval]
  have h0 : D.lam * 0 = 0 := by ring
  rw [h0]
  unfold fq
  rw [zero_pow (Nat.ne_of_gt (Nat.zero_lt_one.trans_le D.hm))]
  ring

/-- g(alpha2) = f0q whenever lam * alpha2 = 1 (n >= 1). -/
theorem gPoly_eval_alpha2 (D : Mzk1ScaleData) (h : D.lam * D.alpha2 = 1) :
    (gPoly D).eval D.alpha2 = f0q D := by
  rw [gPoly_eval, h]
  unfold fq
  rw [show (1 : ℚ) - 1 = 0 by ring, zero_pow (Nat.ne_of_gt (Nat.zero_lt_one.trans_le D.hn))]
  ring

/-- Collapse: g(0) = g(alpha2). -/
theorem gPoly_collapse (D : Mzk1ScaleData) (h : D.lam * D.alpha2 = 1) :
    (gPoly D).eval 0 = (gPoly D).eval D.alpha2 := by
  rw [gPoly_eval_zero, gPoly_eval_alpha2 D h]

#check Mzk1ScaleData
#check fq
#check f0q
#check scale_lemma21_d
#check fq_coe
#check f0q_coe
#check gPoly
#check gPoly_eval
#check gPoly_eval_zero
#check gPoly_eval_alpha2
#check gPoly_collapse
#check mzk1GChoiceConstructRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
end
