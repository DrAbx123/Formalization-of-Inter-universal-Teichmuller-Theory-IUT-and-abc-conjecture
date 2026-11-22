/-
# Mzk1CritValueInImageFinalActual — FINAL C-point critical-value-in-image theorem for gPoly

STEP 0 prior-art (all green, imported; nothing upstream is re-proved here):
* Mzk1GCriticalPointCasesActual
    gPoly_critical_point_cases : aeval z (derivative (gPoly D)) = 0 ->
      z = 0 or z = (D.alpha2 : C) or z = (D.alpha1 : C).
* Mzk1GDerivAevalActual
    gPoly_deriv_aeval_of_any_n : cast-form chain rule over C, evenness-free.
* Mzk1BelyiCvBridgeActual
    belyiPolynomial_critIn01 : C-point critical values of the canonical (NORMALIZED)
      Belyi polynomial B_{m,n} lie in {0,1};  gPoly_eq_belyi21_comp.
* Mzk1Lemma21Actual
    belyi21 := X^m * (X-1)^n  (line 28: UNNORMALIZED),  belyi21_derivative_root.
* Mzk1Lemma22GChoiceConstructActual
    Mzk1ScaleData;  gPoly D = (X^m (X-1)^n).comp (C lam * X) + C (f0q D);
    gPoly_eval / gPoly_eval_zero / gPoly_eval_alpha2.
* Mzk1Lemma22HypPreservationActual
    f0q_eq_zero : Even n -> f0q D = 0  (and every Mzk1ScaleData carries Even n).
* Mzk1GChoiceUnramifiedActual
    lam_mul_alpha1 : lam * alpha1 = r;  fq_zero; fq_one; lam_ne_zero'.
* Mzk1Lemma22CritValueActual
    aeval_cast_eval;  CritValueInImageStatement (the paper Lemma 2.2(i) property).
* TauCeti.Algebra.Polynomial.Belyi
    belyiPolynomial = C ((m+n)^(m+n)/(m^m n^n)) * X^m * (1-X)^n  (NORMALIZED);
    eval_belyiPolynomial, eval_zero_belyiPolynomial, eval_one_belyiPolynomial,
    eval_div_belyiPolynomial, belyiConstant_ne_zero.

NORMALIZATION FACT (decisive for the task): belyi21 is NOT the normalized Belyi
polynomial.  With c = (m+n)^(m+n)/(m^m n^n),
  B_{m,n}(x) = c * x^m (1-x)^n      and      belyi21(x) = (-1)^n * c^{-1} * B_{m,n}(x).
So gPoly is exactly the paper's polynomial f(lam*x) + f0 of Lemma 2.1 (lines 53-64);
its C-critical values are {f0, f0, f(r)+f0}, NOT {0,1}.

DELIVERED (all PROVED here by assembling the upstream facts; no sorry / new axiom /
PUnit / True placeholder):

(1) Values at the three critical points over C:
      gPoly_aeval_zero      : gPoly(0)      = f0q
      gPoly_aeval_alpha2    : gPoly(alpha2) = f0q
      gPoly_aeval_alpha1    : gPoly(alpha1) = fq(m,n,r) + f0q
    and, since every D has Even D.n (f0q = 0, r = m/(m+n)):
      gPoly_aeval_zero_of_even, gPoly_aeval_alpha2_of_even,
      gPoly_aeval_alpha1_of_even : gPoly(alpha1) = critFrac D
    with critFrac D = m^m n^n/(m+n)^(m+n) (the explicit rational value).

(2) The requested 0/1 statement: the TWO BRANCHES THAT ARE TRUE (PROVED):
      gPoly_critValue_eq_zero_of_eq_zero, gPoly_critValue_eq_zero_of_eq_alpha2,
      gPoly_critValue_first_two_branches :
        critical z and (z = 0 or z = alpha2) -> gPoly(z) = 0.

(3) The exact C-critical value set (PROVED):
      gPoly_critValue_zero_or_critFrac : critical -> value = 0 or value = critFrac D,
      gPoly_criticalValues_subset      : C-critical values are contained in {0, critFrac D},
      gPoly_critValue_mem_zero_one_or_eq_alpha1 : value in {0,1} unless z = alpha1.

(4) THE BLOCKER (the literal 0/1 target is FALSE, kernel-checked):
      gPoly_deriv_aeval_alpha1 : alpha1 IS a critical point of gPoly for every D;
      critFrac_pos, critFrac_lt_one : 0 < m^m n^n/(m+n)^(m+n) < 1;
      gPoly_aeval_alpha1_ne_zero, gPoly_aeval_alpha1_ne_one;
      criticalValueInImageStatement_false : the literal statement
        (forall z, critical -> value = 0 or value = 1) is FALSE;
      gPoly_critValue_zero_one_target_false / gPoly_critValue_counterexample.

(5) The TRUE final C-point critical-value-in-image theorem (paper item (i)):
      critValueInImageFinal : CritValueInImageStatement
    every C-critical value of gPoly is gPoly(p) for an explicit p in the source set S
    (p = 0, alpha2 or alpha1).  This is the statement the restated Lemma 2.2 consumer
    (StepProviderStatement: "C-point CV-in-image property") actually needs.

(6) The REPAIRED 0/1 statement (the normalization the literal target assumed):
      belyiNormGPoly_critValue_zero_or_one : for the Belyi-normalized polynomial
        belyiNormGPoly D = C c * gPoly D  (= B_{m,n}(lam * X), even n),
      every C-critical value is 0 or 1.

HONEST SCOPE: the literal target of the task is not merely unproved, it is refuted
(4).  Any consumer asking for critical values in {0,1} must either use (5) (the paper's
item (i), already the form used downstream) or the normalized polynomial of (6).
-/
import tmp.sheaf.xif.paper.Mzk1GCriticalPointCasesActual
import tmp.sheaf.xif.paper.Mzk1Lemma22CritValueActual
import tmp.sheaf.xif.paper.Mzk1Lemma22HypPreservationActual
import tmp.sheaf.xif.paper.Mzk1GChoiceUnramifiedActual
import tmp.sheaf.xif.paper.Mzk1BelyiCvBridgeActual
import tmp.sheaf.xif.paper.RestatedLemma24InterfaceActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1CritValueInImageFinalActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21Actual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceUnramifiedActual
open LeanFormal.IUT.XiFPaper.Mzk1GCriticalPointCasesActual
open LeanFormal.IUT.XiFPaper.Mzk1BelyiCvBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22CritValueActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22HypPreservationActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open TauCeti
/-! ## 1. Values of gPoly at the three critical points -/

/-- The third C-critical value of gPoly as an explicit rational number:
(m^m * n^n) / (m + n)^(m + n).  For every D with Even n, gPoly maps the critical
point alpha1 to this value (gPoly_aeval_alpha1_of_even). -/
def critFrac (D : Mzk1ScaleData) : ℚ :=
  ((D.m ^ D.m * D.n ^ D.n : ℕ) : ℚ) / (((D.m + D.n) ^ (D.m + D.n) : ℕ) : ℚ)

/-- **Value of gPoly at z = 0:** f0q (the paper's f(0) + f0). -/
theorem gPoly_aeval_zero (D : Mzk1ScaleData) :
    Polynomial.aeval (0 : ℂ) (gPoly D) = ((f0q D : ℚ) : ℂ) := by
  have h0 : (0 : ℂ) = ((0 : ℚ) : ℂ) := by norm_num
  rw [h0, aeval_cast_eval, gPoly_eval_zero]

/-- **Value of gPoly at z = alpha2:** f0q (the paper's f(1) + f0). -/
theorem gPoly_aeval_alpha2 (D : Mzk1ScaleData) :
    Polynomial.aeval ((D.alpha2 : ℚ) : ℂ) (gPoly D) = ((f0q D : ℚ) : ℂ) := by
  rw [aeval_cast_eval, gPoly_eval_alpha2 D D.hlam_alpha2]

/-- **Value of gPoly at z = alpha1:** fq(m,n,r) + f0q. -/
theorem gPoly_aeval_alpha1 (D : Mzk1ScaleData) :
    Polynomial.aeval ((D.alpha1 : ℚ) : ℂ) (gPoly D) =
      ((fq D.m D.n D.r + f0q D : ℚ) : ℂ) := by
  rw [aeval_cast_eval, gPoly_eval, lam_mul_alpha1 D]

/-- The scale-data ratio r equals m/(m+n) over Q (cast down from D.hr_eq). -/
theorem r_eq_div (D : Mzk1ScaleData) :
    D.r = (D.m : ℚ) / ((D.m + D.n : ℕ) : ℚ) := by
  rw [D.r_eq]
  have h := D.hr_eq
  rw [D.r_eq] at h
  have hQ : ((D.alpha1 / D.alpha2 : ℚ) : ℝ) =
      (((D.m : ℚ) / ((D.m + D.n : ℕ) : ℚ)) : ℝ) := by
    rw [h]
    push_cast
    ring
  exact_mod_cast hQ

/-- fq(m,n,r) = (m^m * n^n)/(m+n)^(m+n) at r = m/(m+n), for even n. -/
theorem fq_div_eq {m n : ℕ} (hm : 1 ≤ m) (hne : Even n) :
    fq m n ((m : ℚ) / ((m + n : ℕ) : ℚ)) =
      ((m ^ m * n ^ n : ℕ) : ℚ) / (((m + n : ℕ) ^ (m + n) : ℕ) : ℚ) := by
  have hN : ((m + n : ℕ) : ℚ) ≠ 0 := by
    have hpos : (0 : ℕ) < m + n := Nat.add_pos_left (Nat.zero_lt_one.trans_le hm) n
    exact_mod_cast (Nat.ne_of_gt hpos)
  unfold fq
  have hsub : (m : ℚ) / ((m + n : ℕ) : ℚ) - 1 =
      -((n : ℚ) / ((m + n : ℕ) : ℚ)) := by
    field_simp
    push_cast
    ring
  rw [hsub, Even.neg_pow hne]
  rw [div_pow, div_pow, div_mul_div_comm, ← pow_add]
  push_cast
  ring

/-- gPoly(0) = 0 for even n. -/
theorem gPoly_aeval_zero_of_even (D : Mzk1ScaleData) (hne : Even D.n) :
    Polynomial.aeval (0 : ℂ) (gPoly D) = 0 := by
  rw [gPoly_aeval_zero, f0q_eq_zero D hne]
  norm_num

/-- gPoly(alpha2) = 0 for even n. -/
theorem gPoly_aeval_alpha2_of_even (D : Mzk1ScaleData) (hne : Even D.n) :
    Polynomial.aeval ((D.alpha2 : ℚ) : ℂ) (gPoly D) = 0 := by
  rw [gPoly_aeval_alpha2, f0q_eq_zero D hne]
  norm_num

/-- **gPoly(alpha1) = m^m n^n/(m+n)^(m+n)** for even n (in particular for every
Mzk1ScaleData, which carries Even n). -/
theorem gPoly_aeval_alpha1_of_even (D : Mzk1ScaleData) (hne : Even D.n) :
    Polynomial.aeval ((D.alpha1 : ℚ) : ℂ) (gPoly D) = ((critFrac D : ℚ) : ℂ) := by
  rw [gPoly_aeval_alpha1, r_eq_div D, fq_div_eq D.hm hne, f0q_eq_zero D hne, add_zero]
  simp [critFrac]

/-- Same value in fully explicit form. -/
theorem gPoly_aeval_alpha1_of_even_explicit (D : Mzk1ScaleData) (hne : Even D.n) :
    Polynomial.aeval ((D.alpha1 : ℚ) : ℂ) (gPoly D) =
      (((D.m ^ D.m * D.n ^ D.n : ℕ) : ℚ) : ℂ) /
        ((((D.m + D.n) ^ (D.m + D.n) : ℕ) : ℚ) : ℂ) := by
  simpa [critFrac] using gPoly_aeval_alpha1_of_even D hne

/-! ## 2. The third value lies strictly between 0 and 1 -/

/-- m^m * n^n < (m+n)^(m+n) for m, n >= 1. -/
theorem pow_mul_pow_lt_pow_add {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    m ^ m * n ^ n < (m + n) ^ (m + n) := by
  have hmpos : 0 < m := by omega
  have hnpos : 0 < n := by omega
  have h1 : m ^ m < (m + n) ^ m :=
    Nat.pow_lt_pow_left (by omega : m < m + n) (by omega : m ≠ 0)
  have h2 : n ^ n ≤ (m + n) ^ n :=
    Nat.pow_le_pow_left (by omega : n ≤ m + n) n
  calc m ^ m * n ^ n < (m + n) ^ m * n ^ n :=
        Nat.mul_lt_mul_of_pos_right h1 (pow_pos hnpos n)
    _ ≤ (m + n) ^ m * (m + n) ^ n := Nat.mul_le_mul_left _ h2
    _ = (m + n) ^ (m + n) := by rw [← pow_add]

theorem critFrac_pos (D : Mzk1ScaleData) : 0 < critFrac D := by
  have hmpos : (0 : ℕ) < D.m := Nat.zero_lt_one.trans_le D.hm
  have hnpos : (0 : ℕ) < D.n := Nat.zero_lt_one.trans_le D.hn
  have hNpos : (0 : ℕ) < D.m + D.n := Nat.add_pos_left hmpos D.n
  have hm0 : (0 : ℚ) < (D.m : ℚ) := by exact_mod_cast hmpos
  have hn0 : (0 : ℚ) < (D.n : ℚ) := by exact_mod_cast hnpos
  have hN0 : (0 : ℚ) < (((D.m + D.n) ^ (D.m + D.n) : ℕ) : ℚ) := by
    have h' : (0 : ℚ) < ((D.m + D.n : ℕ) : ℚ) := by exact_mod_cast hNpos
    rw [Nat.cast_pow]
    exact pow_pos h' _
  have hnum : (0 : ℚ) < ((D.m ^ D.m * D.n ^ D.n : ℕ) : ℚ) := by
    have h : ((D.m ^ D.m * D.n ^ D.n : ℕ) : ℚ) =
        (D.m : ℚ) ^ D.m * (D.n : ℚ) ^ D.n := by
      push_cast
      ring
    rw [h]
    exact mul_pos (pow_pos hm0 D.m) (pow_pos hn0 D.n)
  unfold critFrac
  exact div_pos hnum hN0

theorem critFrac_lt_one (D : Mzk1ScaleData) : critFrac D < 1 := by
  have hlt := pow_mul_pow_lt_pow_add D.hm D.hn
  have hcast : ((D.m ^ D.m * D.n ^ D.n : ℕ) : ℚ) <
      (((D.m + D.n) ^ (D.m + D.n) : ℕ) : ℚ) := by
    exact_mod_cast hlt
  have hN0 : (0 : ℚ) < (((D.m + D.n) ^ (D.m + D.n) : ℕ) : ℚ) := by
    have hpos : (0 : ℚ) < ((D.m + D.n : ℕ) : ℚ) := by
      exact_mod_cast (Nat.add_pos_left (Nat.zero_lt_one.trans_le D.hm) D.n)
    rw [Nat.cast_pow]
    exact pow_pos hpos _
  unfold critFrac
  rw [div_lt_one hN0]
  exact hcast

theorem critFrac_ne_zero (D : Mzk1ScaleData) : critFrac D ≠ 0 := (critFrac_pos D).ne'
theorem critFrac_ne_one (D : Mzk1ScaleData) : critFrac D ≠ 1 := (critFrac_lt_one D).ne
/-! ## 3. Exact critical-value dichotomy and the two true 0/1 branches -/

/-- **Exact C-critical value set:** every C-critical value of gPoly is 0 or
m^m n^n/(m+n)^(m+n). -/
theorem gPoly_critValue_zero_or_critFrac (D : Mzk1ScaleData) {z : ℂ}
    (hz : Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0) :
    Polynomial.aeval z (gPoly D) = 0 ∨
      Polynomial.aeval z (gPoly D) = ((critFrac D : ℚ) : ℂ) := by
  rcases gPoly_critical_point_cases D hz with h | h | h
  · left
    rw [h, gPoly_aeval_zero_of_even D D.hn_even]
  · left
    rw [h, gPoly_aeval_alpha2_of_even D D.hn_even]
  · right
    rw [h, gPoly_aeval_alpha1_of_even D D.hn_even]

/-- Set form of gPoly_critValue_zero_or_critFrac. -/
theorem gPoly_criticalValues_subset (D : Mzk1ScaleData) :
    {v : ℂ | ∃ z : ℂ, Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0 ∧
        Polynomial.aeval z (gPoly D) = v} ⊆
      ({0, ((critFrac D : ℚ) : ℂ)} : Set ℂ) := by
  rintro v ⟨z, hz, rfl⟩
  rcases gPoly_critValue_zero_or_critFrac D hz with h | h <;> simp [h]

/-- **Branch 1 (PROVED):** z = 0 gives value 0. -/
theorem gPoly_critValue_eq_zero_of_eq_zero (D : Mzk1ScaleData) {z : ℂ}
    (h : z = 0) : Polynomial.aeval z (gPoly D) = 0 := by
  rw [h, gPoly_aeval_zero_of_even D D.hn_even]

/-- **Branch 2 (PROVED):** z = alpha2 gives value 0. -/
theorem gPoly_critValue_eq_zero_of_eq_alpha2 (D : Mzk1ScaleData) {z : ℂ}
    (h : z = ((D.alpha2 : ℚ) : ℂ)) : Polynomial.aeval z (gPoly D) = 0 := by
  rw [h, gPoly_aeval_alpha2_of_even D D.hn_even]

/-- **The two true branches of the requested 0/1 statement:** a critical point that is
0 or alpha2 has value 0. -/
theorem gPoly_critValue_first_two_branches (D : Mzk1ScaleData) {z : ℂ}
    (_hz : Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0)
    (h0 : z = 0 ∨ z = ((D.alpha2 : ℚ) : ℂ)) :
    Polynomial.aeval z (gPoly D) = 0 := by
  rcases h0 with h | h
  · exact gPoly_critValue_eq_zero_of_eq_zero D h
  · exact gPoly_critValue_eq_zero_of_eq_alpha2 D h

/-- The 0/1 conclusion holds for every C-critical point EXCEPT possibly alpha1. -/
theorem gPoly_critValue_mem_zero_one_or_eq_alpha1 (D : Mzk1ScaleData) {z : ℂ}
    (hz : Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0) :
    Polynomial.aeval z (gPoly D) ∈ ({0, 1} : Set ℂ) ∨ z = ((D.alpha1 : ℚ) : ℂ) := by
  rcases gPoly_critical_point_cases D hz with h | h | h
  · left
    rw [h, gPoly_aeval_zero_of_even D D.hn_even]
    simp
  · left
    rw [h, gPoly_aeval_alpha2_of_even D D.hn_even]
    simp
  · right
    exact h

/-! ## 4. The third branch: alpha1 is critical and its value is neither 0 nor 1 -/

/-- The derivative of the unnormalized Belyi polynomial belyi21 at a C-point. -/
theorem aeval_derivative_belyi21 (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (x : ℂ) :
    Polynomial.aeval x (Polynomial.derivative (belyi21 m n)) =
      x ^ (m - 1) * (x - 1) ^ (n - 1) * (((m + n : ℕ) : ℂ) * x - (m : ℂ)) := by
  rw [belyi21_derivative m n hm hn]
  simp only [map_mul, map_pow, map_sub, aeval_X, aeval_C, map_one]
  push_cast
  ring

/-- belyi21'(m/(m+n)) = 0, i.e. m/(m+n) is a C-critical point of belyi21. -/
theorem aeval_derivative_belyi21_at_div (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    Polynomial.aeval ((m : ℂ) / ((m : ℂ) + (n : ℂ)))
      (Polynomial.derivative (belyi21 m n)) = 0 := by
  rw [aeval_derivative_belyi21 m n hm hn]
  have hden : (m : ℂ) + (n : ℂ) ≠ 0 := by
    have hpos : (0 : ℕ) < m + n := Nat.add_pos_left (Nat.zero_lt_one.trans_le hm) n
    have hcast : ((m + n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hpos)
    simpa using hcast
  have hx : ((m + n : ℕ) : ℂ) * ((m : ℂ) / ((m : ℂ) + (n : ℂ))) - (m : ℂ) = 0 := by
    have hcast : ((m + n : ℕ) : ℂ) = (m : ℂ) + (n : ℂ) := by
      push_cast
      ring
    rw [hcast, mul_div_cancel₀ (m : ℂ) hden, sub_self]
  rw [hx, mul_zero]

/-- Cast of lam * alpha1 = r = m/(m+n). -/
theorem cast_lam_mul_alpha1 (D : Mzk1ScaleData) :
    (D.lam : ℂ) * ((D.alpha1 : ℚ) : ℂ) = (D.m : ℂ) / ((D.m : ℂ) + (D.n : ℂ)) := by
  have h1 : (D.lam : ℂ) * ((D.alpha1 : ℚ) : ℂ) = ((D.r : ℚ) : ℂ) := by
    calc (D.lam : ℂ) * ((D.alpha1 : ℚ) : ℂ) =
          ((D.lam * D.alpha1 : ℚ) : ℂ) := by
          push_cast
          ring
      _ = ((D.r : ℚ) : ℂ) := by rw [lam_mul_alpha1 D]
  rw [h1, r_eq_div D]
  push_cast
  ring

/-- **alpha1 is a critical point of gPoly for every scale datum.** -/
theorem gPoly_deriv_aeval_alpha1 (D : Mzk1ScaleData) :
    Polynomial.aeval ((D.alpha1 : ℚ) : ℂ) (Polynomial.derivative (gPoly D)) = 0 := by
  rw [Mzk1GDerivAevalActual.gPoly_deriv_aeval_of_any_n D ((D.alpha1 : ℚ) : ℂ),
    cast_lam_mul_alpha1 D, aeval_derivative_belyi21_at_div D.m D.n D.hm D.hn, mul_zero]

/-- The value at the always-critical point alpha1 is nonzero. -/
theorem gPoly_aeval_alpha1_ne_zero (D : Mzk1ScaleData) :
    Polynomial.aeval ((D.alpha1 : ℚ) : ℂ) (gPoly D) ≠ 0 := by
  rw [gPoly_aeval_alpha1_of_even D D.hn_even]
  intro h
  have h0 : ((critFrac D : ℚ) : ℂ) = ((0 : ℚ) : ℂ) := by simpa using h
  exact critFrac_ne_zero D (Rat.cast_injective h0)

/-- The value at the always-critical point alpha1 is not 1. -/
theorem gPoly_aeval_alpha1_ne_one (D : Mzk1ScaleData) :
    Polynomial.aeval ((D.alpha1 : ℚ) : ℂ) (gPoly D) ≠ 1 := by
  rw [gPoly_aeval_alpha1_of_even D D.hn_even]
  intro h
  have h1 : ((critFrac D : ℚ) : ℂ) = ((1 : ℚ) : ℂ) := by simpa using h
  exact critFrac_ne_one D (Rat.cast_injective h1)

/-- The literal requested 0/1 statement, as a named (FALSE) proposition. -/
def CriticalValueInImageStatement (D : Mzk1ScaleData) : Prop :=
  ∀ z : ℂ, Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0 →
    Polynomial.aeval z (gPoly D) ∈ ({0, 1} : Set ℂ)

/-- **BLOCKER (kernel-checked):** the literal requested 0/1 target is FALSE for every
scale datum; the witness is the always-critical point alpha1. -/
theorem criticalValueInImageStatement_false (D : Mzk1ScaleData) :
    ¬ CriticalValueInImageStatement D := by
  intro H
  have h := H ((D.alpha1 : ℚ) : ℂ) (gPoly_deriv_aeval_alpha1 D)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  rcases h with h | h
  · exact gPoly_aeval_alpha1_ne_zero D h
  · exact gPoly_aeval_alpha1_ne_one D h

/-- Same refutation in the explicit disjunction form (for fixed D). -/
theorem gPoly_critValue_zero_one_target_false (D : Mzk1ScaleData) :
    ¬ (∀ z : ℂ, Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0 →
        Polynomial.aeval z (gPoly D) = 0 ∨ Polynomial.aeval z (gPoly D) = 1) := by
  intro H
  exact criticalValueInImageStatement_false D (fun z hz => by
    rcases H z hz with h | h <;> simp [h])

/-- Counterexample form of the blocker. -/
theorem gPoly_critValue_counterexample (D : Mzk1ScaleData) :
    ∃ z : ℂ, Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0 ∧
      Polynomial.aeval z (gPoly D) ≠ 0 ∧ Polynomial.aeval z (gPoly D) ≠ 1 :=
  ⟨((D.alpha1 : ℚ) : ℂ), gPoly_deriv_aeval_alpha1 D,
    gPoly_aeval_alpha1_ne_zero D, gPoly_aeval_alpha1_ne_one D⟩

/-- The fully universally quantified form of the requested target is false as soon as
one scale datum exists. -/
theorem zeroOneUniversal_target_false (h : Nonempty Mzk1ScaleData) :
    ¬ (∀ (D : Mzk1ScaleData) (z : ℂ),
        Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0 →
          Polynomial.aeval z (gPoly D) = 0 ∨ Polynomial.aeval z (gPoly D) = 1) := by
  obtain ⟨D⟩ := h
  intro H
  exact gPoly_critValue_zero_one_target_false D (fun z hz => H D z hz)
/-! ## 5. The final C-point critical-value-in-image theorem (paper Lemma 2.2 item (i)) -/

/-- **FINAL (paper item (i)):** every C-point critical value of gPoly is the value of
gPoly at a point of the source set S (explicitly p = 0, alpha2 or alpha1). -/
theorem critValueInImageFinal : CritValueInImageStatement := by
  intro D H z hz
  rcases gPoly_critical_point_cases D hz with h | h | h
  · refine ⟨P1Point.ofFinite (0 : ℚ), H.1, f0q D, ?_, ?_⟩
    · rw [h, gPoly_aeval_zero]
    · show polyEvalP1 (gPoly D) (P1Point.ofFinite (0 : ℚ)) = P1Point.ofFinite (f0q D)
      rw [show polyEvalP1 (gPoly D) (P1Point.ofFinite (0 : ℚ)) =
        P1Point.ofFinite ((gPoly D).eval 0) from rfl, gPoly_eval_zero]
  · refine ⟨P1Point.ofFinite D.alpha2, D.halpha2S, f0q D, ?_, ?_⟩
    · rw [h, gPoly_aeval_alpha2]
    · show polyEvalP1 (gPoly D) (P1Point.ofFinite D.alpha2) = P1Point.ofFinite (f0q D)
      rw [show polyEvalP1 (gPoly D) (P1Point.ofFinite D.alpha2) =
        P1Point.ofFinite ((gPoly D).eval D.alpha2) from rfl,
        gPoly_eval_alpha2 D D.hlam_alpha2]
  · refine ⟨P1Point.ofFinite D.alpha1, D.halpha1S, fq D.m D.n D.r + f0q D, ?_, ?_⟩
    · rw [h, gPoly_aeval_alpha1]
    · show polyEvalP1 (gPoly D) (P1Point.ofFinite D.alpha1) =
        P1Point.ofFinite (fq D.m D.n D.r + f0q D)
      rw [show polyEvalP1 (gPoly D) (P1Point.ofFinite D.alpha1) =
        P1Point.ofFinite ((gPoly D).eval D.alpha1) from rfl, gPoly_eval, lam_mul_alpha1 D]

/-- Pointwise form of the final theorem (the shape consumed downstream). -/
theorem critValueInImageFinal_pointwise (D : Mzk1ScaleData)
    (H : Lemma22Hypotheses D.S D.beta) (z : ℂ)
    (hz : Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0) :
    ∃ p ∈ D.S, ∃ v : ℚ, (v : ℂ) = Polynomial.aeval z (gPoly D) ∧
      polyEvalP1 (gPoly D) p = P1Point.ofFinite v :=
  critValueInImageFinal D H z hz

/-! ## 6. Repaired 0/1 statement: the Belyi-normalized polynomial -/

/-- The normalizing constant of the canonical Belyi polynomial
B_{m,n} = C c * X^m * (1 - X)^n. -/
def belyiNormConst (m n : ℕ) : ℚ :=
  (((m + n) ^ (m + n) : ℕ) : ℚ) / ((m ^ m * n ^ n : ℕ) : ℚ)

/-- belyiNormConst in the exact syntactic form used by belyiPolynomial. -/
theorem belyiNormConst_eq (m n : ℕ) :
    belyiNormConst m n = (((m : ℚ) + n) ^ (m + n)) / ((m : ℚ) ^ m * (n : ℚ) ^ n) := by
  unfold belyiNormConst
  push_cast
  ring

theorem belyiNormConst_ne_zero (m n : ℕ) : belyiNormConst m n ≠ 0 := by
  rw [belyiNormConst_eq]
  exact belyiConstant_ne_zero (K := ℚ) m n

/-- For even n, c * belyi21 is the canonical Belyi polynomial B_{m,n}. -/
theorem C_belyiNormConst_mul_belyi21 {m n : ℕ} (hne : Even n) :
    Polynomial.C (belyiNormConst m n) * belyi21 m n = belyiPolynomial ℚ m n := by
  unfold belyi21 belyiPolynomial
  rw [belyiNormConst_eq]
  have h1 : (1 - (Polynomial.X : ℚ[X])) ^ n =
      ((Polynomial.X : ℚ[X]) - Polynomial.C 1) ^ n := by
    have hneg : (1 - (Polynomial.X : ℚ[X])) =
        -((Polynomial.X : ℚ[X]) - Polynomial.C 1) := by
      rw [Polynomial.C_1]
      ring
    rw [hneg, Even.neg_pow hne]
  rw [h1, mul_assoc]

/-- For even n, the Belyi-normalized gPoly is B_{m,n}(lam * X). -/
theorem C_belyiNormConst_mul_gPoly_eq_comp (D : Mzk1ScaleData) (hne : Even D.n) :
    Polynomial.C (belyiNormConst D.m D.n) * gPoly D =
      (belyiPolynomial ℚ D.m D.n).comp (Polynomial.C D.lam * Polynomial.X) := by
  calc Polynomial.C (belyiNormConst D.m D.n) * gPoly D
      = Polynomial.C (belyiNormConst D.m D.n) *
          (belyi21 D.m D.n).comp (Polynomial.C D.lam * Polynomial.X) := by
        rw [gPoly_eq_belyi21_comp D hne]
    _ = (Polynomial.C (belyiNormConst D.m D.n) * belyi21 D.m D.n).comp
          (Polynomial.C D.lam * Polynomial.X) := by
        rw [Polynomial.mul_comp, Polynomial.C_comp]
    _ = (belyiPolynomial ℚ D.m D.n).comp (Polynomial.C D.lam * Polynomial.X) := by
        rw [C_belyiNormConst_mul_belyi21 hne]

/-- The Belyi-normalized g-choice polynomial. -/
def belyiNormGPoly (D : Mzk1ScaleData) : ℚ[X] :=
  Polynomial.C (belyiNormConst D.m D.n) * gPoly D

theorem aeval_C_mul_rat (c : ℚ) (z : ℂ) (p : ℚ[X]) :
    Polynomial.aeval z (Polynomial.C c * p) = ((c : ℚ) : ℂ) * Polynomial.aeval z p := by
  rw [Polynomial.aeval_mul, Polynomial.aeval_C]
  rfl

theorem belyiNormGPoly_aeval (D : Mzk1ScaleData) (z : ℂ) :
    Polynomial.aeval z (belyiNormGPoly D) =
      ((belyiNormConst D.m D.n : ℚ) : ℂ) * Polynomial.aeval z (gPoly D) := by
  unfold belyiNormGPoly
  exact aeval_C_mul_rat _ z _

/-- c * (m^m n^n/(m+n)^(m+n)) = 1 over Q. -/
theorem belyiNormConst_mul_critFrac (D : Mzk1ScaleData) :
    belyiNormConst D.m D.n * critFrac D = 1 := by
  unfold belyiNormConst critFrac
  have hA : ((D.m ^ D.m * D.n ^ D.n : ℕ) : ℚ) ≠ 0 := by
    have hmpos : (0 : ℕ) < D.m := Nat.zero_lt_one.trans_le D.hm
    have hnpos : (0 : ℕ) < D.n := Nat.zero_lt_one.trans_le D.hn
    have hm0 : (0 : ℚ) < (D.m : ℚ) := by exact_mod_cast hmpos
    have hn0 : (0 : ℚ) < (D.n : ℚ) := by exact_mod_cast hnpos
    have h : ((D.m ^ D.m * D.n ^ D.n : ℕ) : ℚ) =
        (D.m : ℚ) ^ D.m * (D.n : ℚ) ^ D.n := by
      push_cast
      ring
    rw [h]
    exact (mul_pos (pow_pos hm0 D.m) (pow_pos hn0 D.n)).ne'
  have hB : (((D.m + D.n) ^ (D.m + D.n) : ℕ) : ℚ) ≠ 0 := by
    have hpos : (0 : ℚ) < ((D.m + D.n : ℕ) : ℚ) := by
      exact_mod_cast (Nat.add_pos_left (Nat.zero_lt_one.trans_le D.hm) D.n)
    rw [Nat.cast_pow]
    exact (pow_pos hpos _).ne'
  rw [div_mul_div_comm,
    mul_comm (((D.m + D.n) ^ (D.m + D.n) : ℕ) : ℚ) ((D.m ^ D.m * D.n ^ D.n : ℕ) : ℚ),
    div_self (mul_ne_zero hA hB)]

theorem belyiNormConst_cast_mul_critFrac_cast (D : Mzk1ScaleData) :
    ((belyiNormConst D.m D.n : ℚ) : ℂ) * ((critFrac D : ℚ) : ℂ) = 1 := by
  have h := congrArg (fun q : ℚ => ((q : ℂ))) (belyiNormConst_mul_critFrac D)
  simpa using h

/-- **REPAIRED (PROVED) 0/1 statement:** for the Belyi-normalized polynomial
belyiNormGPoly D = C c * gPoly D, every C-critical value is 0 or 1. -/
theorem belyiNormGPoly_critValue_zero_or_one (D : Mzk1ScaleData) (z : ℂ)
    (hz : Polynomial.aeval z (Polynomial.derivative (belyiNormGPoly D)) = 0) :
    Polynomial.aeval z (belyiNormGPoly D) = 0 ∨
      Polynomial.aeval z (belyiNormGPoly D) = 1 := by
  have hc : ((belyiNormConst D.m D.n : ℚ) : ℂ) ≠ 0 := by
    intro h
    have h0 : ((belyiNormConst D.m D.n : ℚ) : ℂ) = ((0 : ℚ) : ℂ) := by simpa using h
    exact belyiNormConst_ne_zero D.m D.n (Rat.cast_injective h0)
  have hder : Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0 := by
    have h := hz
    unfold belyiNormGPoly at h
    rw [Polynomial.derivative_C_mul, aeval_C_mul_rat] at h
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 hc
    · exact h0
  rcases gPoly_critValue_zero_or_critFrac D hder with h | h
  · left
    rw [belyiNormGPoly_aeval, h, mul_zero]
  · right
    rw [belyiNormGPoly_aeval, h, belyiNormConst_cast_mul_critFrac_cast D]

/-- The repaired target in set-membership form. -/
def CorrectedZeroOneStatement (D : Mzk1ScaleData) : Prop :=
  ∀ z : ℂ, Polynomial.aeval z (Polynomial.derivative (belyiNormGPoly D)) = 0 →
    Polynomial.aeval z (belyiNormGPoly D) ∈ ({0, 1} : Set ℂ)

theorem correctedZeroOneStatement_proved (D : Mzk1ScaleData) :
    CorrectedZeroOneStatement D := by
  intro z hz
  rcases belyiNormGPoly_critValue_zero_or_one D z hz with h | h <;> simp [h]

/-! ## 7. Ledger, blocker and consistency checks -/

structure CritValueFinalRow where
  item : String
  status : String
  proved : Bool

def critValueFinalRows : List CritValueFinalRow :=
  [ ⟨"chain rule over C (evenness-free)", "REUSED Mzk1GDerivAevalActual.gPoly_deriv_aeval_of_any_n", true⟩
  , ⟨"critical points of gPoly are 0 / alpha2 / alpha1", "REUSED gPoly_critical_point_cases", true⟩
  , ⟨"values at 0 / alpha2 / alpha1 over C", "PROVED gPoly_aeval_zero / gPoly_aeval_alpha2 / gPoly_aeval_alpha1", true⟩
  , ⟨"even-n values 0, 0, m^m n^n/(m+n)^(m+n)", "PROVED gPoly_aeval_zero_of_even / gPoly_aeval_alpha2_of_even / gPoly_aeval_alpha1_of_even", true⟩
  , ⟨"two true branches: z = 0 or z = alpha2 gives value 0", "PROVED gPoly_critValue_first_two_branches", true⟩
  , ⟨"exact C-critical value set {0, critFrac D}", "PROVED gPoly_critValue_zero_or_critFrac / gPoly_criticalValues_subset", true⟩
  , ⟨"third branch: alpha1 is critical, value strictly in (0,1)", "PROVED gPoly_deriv_aeval_alpha1 / critFrac_pos / critFrac_lt_one", true⟩
  , ⟨"literal 0/1 target for gPoly", "REFUTED criticalValueInImageStatement_false (every D)", false⟩
  , ⟨"final C-point critical-value-in-image (paper item (i))", "PROVED critValueInImageFinal : CritValueInImageStatement", true⟩
  , ⟨"repaired 0/1 statement for the Belyi-normalized polynomial", "PROVED belyiNormGPoly_critValue_zero_or_one", true⟩ ]

theorem critValueFinalRows_length : critValueFinalRows.length = 10 := rfl

/-- The blocker, in one line: the unnormalized gPoly has a third critical value strictly
between 0 and 1, so the literal 0/1 target is false. -/
def critValueFinalBlocker : String :=
  "REFUTED, not unproved: belyi21 = X^m (X-1)^n is unnormalized, so the critical point " ++
  "alpha1 (lam * alpha1 = r = m/(m+n)) has value m^m n^n/(m+n)^(m+n), strictly inside " ++
  "(0,1) (critFrac_pos, critFrac_lt_one), for EVERY Mzk1ScaleData. " ++
  "Use critValueInImageFinal (paper item (i)) or belyiNormGPoly_critValue_zero_or_one."

#check gPoly_aeval_zero
#check gPoly_aeval_alpha2
#check gPoly_aeval_alpha1
#check gPoly_aeval_zero_of_even
#check gPoly_aeval_alpha2_of_even
#check gPoly_aeval_alpha1_of_even
#check gPoly_aeval_alpha1_of_even_explicit
#check gPoly_critValue_zero_or_critFrac
#check gPoly_criticalValues_subset
#check gPoly_critValue_first_two_branches
#check gPoly_critValue_mem_zero_one_or_eq_alpha1
#check gPoly_deriv_aeval_alpha1
#check gPoly_aeval_alpha1_ne_zero
#check gPoly_aeval_alpha1_ne_one
#check criticalValueInImageStatement_false
#check gPoly_critValue_zero_one_target_false
#check gPoly_critValue_counterexample
#check zeroOneUniversal_target_false
#check critValueInImageFinal
#check critValueInImageFinal_pointwise
#check belyiNormGPoly_critValue_zero_or_one
#check correctedZeroOneStatement_proved
#check critValueFinalRows_length

#print axioms gPoly_aeval_alpha1_of_even
#print axioms gPoly_critValue_zero_or_critFrac
#print axioms criticalValueInImageStatement_false
#print axioms critValueInImageFinal
#print axioms belyiNormGPoly_critValue_zero_or_one


end LeanFormal.IUT.XiFPaper.Mzk1CritValueInImageFinalActual
end
