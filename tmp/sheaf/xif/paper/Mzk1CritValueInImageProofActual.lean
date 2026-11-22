/-
# Mzk1CritValueInImageProofActual — C-point critical values of gPoly:
  the true "critical-value-in-image" statement, the Belyi-normalized 0/1 bridge,
  and a kernel-checked refutation of the literal 0/1 target for the unnormalized gPoly.

STEP 0 prior-art (reuse, no re-proof):
* tmp/sheaf/xif/paper/Mzk1BelyiCvBridgeActual.lean
    - belyiPolynomial_critIn01 : over C, every critical point of the canonical Belyi
      polynomial B_{m,n} maps to 0 or 1 (PROVED, via ported TauCeti critical values);
    - gPoly_eq_belyi21_comp : for even n, gPoly D = belyi21 m n comp (lam * X).
* tmp/sheaf/xif/paper/Mzk1Lemma22CritValueActual.lean
    - CritValueInImageStatement : the paper Lemma 2.1(b)/2.2(i) property, namely every
      C-point critical value of gPoly is gPoly(p) for some p in the source set S;
    - aeval_cast_eval.
* tmp/sheaf/xif/paper/Mzk1Lemma21Actual.lean : belyi21, belyi21_derivative,
  belyi21_derivative_root (root dichotomy over C).
* tmp/sheaf/xif/paper/Mzk1Lemma22GChoiceConstructActual.lean : Mzk1ScaleData, gPoly,
  f0q, gPoly_eval_zero, gPoly_eval_alpha2.
* tmp/sheaf/xif/paper/Mzk1GChoiceUnramifiedActual.lean : lam_ne_zero', lam_mul_alpha1.

CONTENT (all PROVED in this file; no forbidden placeholders):
1. the chain-rule formula for d/dt gPoly over C (no even-n hypothesis needed);
2. critValueInImageStatement_proved : the exact statement
   Mzk1Lemma22CritValueActual.CritValueInImageStatement — every C-point critical
   value of gPoly is the value of gPoly at a point of the source S (paper Lemma 2.2(i));
3. the Belyi-bridge critical-value computation for even n:
   if gPoly'(z) = 0 then gPoly(z) = 0 or gPoly(z) = (belyiNormConst m n)^{-1};
4. the normalized 0/1 theorem: for belyiNormGPoly D = C (belyiNormConst m n) * gPoly D
   (which equals (belyiPolynomial ℚ m n).comp (lam * X) for even n) every C-point
   critical value is 0 or 1, by belyiPolynomial_critIn01;
5. REFUTATION of the literal requested target
   forall z, gPoly'(z) = 0 -> gPoly(z) = 0 or gPoly(z) = 1, for EVERY D with Even D.n:
   the explicit critical point z = (m/(m+n)) / lam has value (belyiNormConst m n)^{-1},
   which is neither 0 nor 1, because m^m * n^n < (m+n)^(m+n).

HONEST SCOPE: the literal target of the task is FALSE (not merely unproved); gPoly is the
unnormalized polynomial f(lam * x) + f0 of the paper (Lemma 2.1 lines 53-64), whose third
critical value is f(r) (resp. f(r)+f0), not 1.  The paper's Lemma 2.2 only needs the
critical value to lie in the image g(S) (item 2 above); the 0/1 property holds for the
Belyi-normalized polynomial (item 4 above), which is the correct repair.  Named blocker =
the external spec: the requested statement must be re-stated as item 2 or item 4.
-/
import tmp.sheaf.xif.paper.Mzk1BelyiCvBridgeActual
import tmp.sheaf.xif.paper.Mzk1Lemma22CritValueActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.Mzk1CritValueInImageProofActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21Actual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceUnramifiedActual
open LeanFormal.IUT.XiFPaper.Mzk1BelyiCvBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22CritValueActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open TauCeti

/-! ## 1. The Belyi normalizing constant and the normalized gPoly -/

/-- The normalizing constant of TauCeti's Belyi polynomial
B_{m,n} = C c * X^m * (1 - X)^n. -/
def belyiNormConst (m n : ℕ) : ℚ :=
  (((m : ℚ) + n) ^ (m + n)) / ((m : ℚ) ^ m * (n : ℚ) ^ n)

theorem belyiNormConst_ne_zero (m n : ℕ) : belyiNormConst m n ≠ 0 := by
  unfold belyiNormConst
  exact belyiConstant_ne_zero (K := ℚ) m n

/-- For even n, C c * belyi21 m n = belyiPolynomial ℚ m n. -/
theorem C_belyiNormConst_mul_belyi21 (m n : ℕ) (hne : Even n) :
    C (belyiNormConst m n) * belyi21 m n = belyiPolynomial ℚ m n := by
  unfold belyi21 belyiPolynomial belyiNormConst
  have h1 : (1 - (X : ℚ[X])) ^ n = ((X : ℚ[X]) - 1) ^ n := by
    have hneg : (1 - (X : ℚ[X])) = -((X : ℚ[X]) - 1) := by ring
    rw [hneg, Even.neg_pow hne]
  rw [h1, C_1]
  ring

/-- For even n, the normalized gPoly is the canonical Belyi polynomial precomposed with
lam * X. -/
theorem C_belyiNormConst_mul_gPoly_eq_comp (D : Mzk1ScaleData) (hne : Even D.n) :
    C (belyiNormConst D.m D.n) * gPoly D =
      (belyiPolynomial ℚ D.m D.n).comp (C D.lam * X) := by
  calc C (belyiNormConst D.m D.n) * gPoly D
      = C (belyiNormConst D.m D.n) * (belyi21 D.m D.n).comp (C D.lam * X) := by
        rw [gPoly_eq_belyi21_comp D hne]
    _ = (C (belyiNormConst D.m D.n) * belyi21 D.m D.n).comp (C D.lam * X) := by
        rw [mul_comp, C_comp]
    _ = (belyiPolynomial ℚ D.m D.n).comp (C D.lam * X) := by
        rw [C_belyiNormConst_mul_belyi21 D.m D.n hne]

/-! ## 2. Chain rule / aeval formulas over C -/

/-- p.comp (a * X) evaluated at z equals p evaluated at a * z. -/
theorem aeval_comp_C_mul_X (p : ℚ[X]) (a : ℚ) (z : ℂ) :
    aeval z (p.comp (C a * X)) = aeval ((a : ℂ) * z) p := by
  rw [Polynomial.aeval_comp]
  have h : aeval z ((C a) * X) = (a : ℂ) * z := by
    rw [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    rfl
  rw [h]

/-- Chain rule: the derivative of p.comp (a * X) at z. -/
theorem aeval_derivative_comp_C_mul_X (p : ℚ[X]) (a : ℚ) (z : ℂ) :
    aeval z (derivative (p.comp (C a * X))) =
      (a : ℂ) * aeval ((a : ℂ) * z) (derivative p) := by
  rw [derivative_comp, derivative_C_mul_X]
  rw [Polynomial.aeval_mul, Polynomial.aeval_C, aeval_comp_C_mul_X]
  rfl

/-- Additive decomposition: gPoly is the unnormalized Belyi polynomial precomposed
with lam * X, shifted by f0q (not normalized by the Belyi constant). -/
theorem gPoly_eq_belyi21_comp_add (D : Mzk1ScaleData) :
    gPoly D = (belyi21 D.m D.n).comp (C D.lam * X) + C (f0q D) := by
  unfold gPoly belyi21
  rfl

/-- The chain-rule formula for gPoly over C; valid for every n
(the shift f0q disappears under the derivative). -/
theorem aeval_derivative_gPoly_eq (D : Mzk1ScaleData) (z : ℂ) :
    aeval z (derivative (gPoly D)) =
      (D.lam : ℂ) * aeval ((D.lam : ℂ) * z) (derivative (belyi21 D.m D.n)) := by
  rw [gPoly_eq_belyi21_comp_add]
  rw [derivative_add, derivative_C, add_zero]
  exact aeval_derivative_comp_C_mul_X _ _ _

theorem lam_cast_ne_zero (D : Mzk1ScaleData) : (D.lam : ℂ) ≠ 0 := by
  have h := lam_ne_zero' D
  intro hc
  exact h (Rat.cast_injective (α := ℂ) (by simpa using hc))

/-- The value formula over C (no even-n hypothesis). -/
theorem aeval_belyi21 (m n : ℕ) (x : ℂ) :
    aeval x (belyi21 m n) = x ^ m * (x - 1) ^ n := by
  unfold belyi21
  simp [map_mul, map_pow, map_sub]

/-- The derivative formula over C. -/
theorem aeval_derivative_belyi21 (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (x : ℂ) :
    aeval x (derivative (belyi21 m n)) =
      x ^ (m - 1) * (x - 1) ^ (n - 1) *
        (((m + n : ℕ) : ℂ) * x - (m : ℂ)) := by
  rw [belyi21_derivative m n hm hn]
  simp only [map_mul, map_pow, map_sub, aeval_X, aeval_C, map_one]
  push_cast
  ring

/-! ## 3. The true critical-value-in-image statement (paper Lemma 2.2(i)) -/

/-- Critical points of gPoly over C map into the source set values.  This is exactly
Mzk1Lemma22CritValueActual.CritValueInImageStatement; note that no even-n hypothesis
is needed (the derivative kills the shift f0q). -/
theorem critValueInImageStatement_proved : CritValueInImageStatement := by
  intro D H z hz
  have hlam : (D.lam : ℂ) ≠ 0 := lam_cast_ne_zero D
  have hroot : aeval ((D.lam : ℂ) * z) (derivative (belyi21 D.m D.n)) = 0 := by
    rw [aeval_derivative_gPoly_eq] at hz
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h hlam
    · exact h
  rcases belyi21_derivative_root D.hm D.hn hroot with h0 | h1 | hr
  · -- the critical point lands on 0: value f0q = gPoly(0)
    have hz0 : z = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hlam
      · exact h
    refine ⟨P1Point.ofFinite (0 : ℚ), H.1, f0q D, ?_, ?_⟩
    · rw [hz0]
      rw [show (0 : ℂ) = ((0 : ℚ) : ℂ) by norm_num, aeval_cast_eval, gPoly_eval_zero]
    · change P1Point.ofFinite ((gPoly D).eval (0 : ℚ)) = P1Point.ofFinite (f0q D)
      rw [gPoly_eval_zero]
  · -- the critical point lands on 1: z = alpha2, value f0q = gPoly(alpha2)
    have hcast : (D.lam : ℂ) * ((D.alpha2 : ℚ) : ℂ) = 1 := by
      have h := D.hlam_alpha2
      exact_mod_cast h
    have hzalpha2 : z = ((D.alpha2 : ℚ) : ℂ) := by
      have h : (D.lam : ℂ) * z = (D.lam : ℂ) * ((D.alpha2 : ℚ) : ℂ) := by
        rw [h1, hcast]
      exact mul_left_cancel₀ hlam h
    refine ⟨P1Point.ofFinite D.alpha2, D.halpha2S, f0q D, ?_, ?_⟩
    · rw [hzalpha2, aeval_cast_eval, gPoly_eval_alpha2 D D.hlam_alpha2]
    · change P1Point.ofFinite ((gPoly D).eval D.alpha2) = P1Point.ofFinite (f0q D)
      rw [gPoly_eval_alpha2 D D.hlam_alpha2]
  · -- the critical point lands on r = m/(m+n): z = alpha1, value gPoly(alpha1)
    have hden : (D.m : ℂ) + (D.n : ℂ) ≠ 0 := by
      have hmpos : 0 < D.m := Nat.zero_lt_one.trans_le D.hm
      have hnpos : 0 < D.n := Nat.zero_lt_one.trans_le D.hn
      have hpos : D.m + D.n ≠ 0 := by omega
      have hpos' : ((D.m + D.n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hpos
      simpa using hpos'
    have hsl : (D.lam : ℂ) * z = (D.m : ℂ) / ((D.m : ℂ) + (D.n : ℂ)) := by
      have hr' : ((D.lam : ℂ) * z) * ((D.m : ℂ) + (D.n : ℂ)) = (D.m : ℂ) := by
        have hcast : (((D.m + D.n : ℕ)) : ℂ) = (D.m : ℂ) + (D.n : ℂ) := by
          push_cast
          ring
        rw [← hcast, mul_comm]
        exact hr
      rw [eq_div_iff hden]
      exact hr'
    have hrQ : D.r = (D.m : ℚ) / ((D.m + D.n : ℕ) : ℚ) := by
      have hQ : ((D.r : ℚ) : ℝ) = (((D.m : ℚ) / ((D.m + D.n : ℕ) : ℚ)) : ℝ) := by
        rw [D.hr_eq]
        push_cast
        ring
      exact_mod_cast hQ
    have hrC : ((D.r : ℚ) : ℂ) = (D.m : ℂ) / ((D.m : ℂ) + (D.n : ℂ)) := by
      rw [hrQ]
      push_cast
      ring
    have hlam_alpha1C : (D.lam : ℂ) * ((D.alpha1 : ℚ) : ℂ) = ((D.r : ℚ) : ℂ) := by
      have h := lam_mul_alpha1 D
      exact_mod_cast h
    have hzalpha1 : z = ((D.alpha1 : ℚ) : ℂ) := by
      have h : (D.lam : ℂ) * z = (D.lam : ℂ) * ((D.alpha1 : ℚ) : ℂ) := by
        calc (D.lam : ℂ) * z = (D.m : ℂ) / ((D.m : ℂ) + (D.n : ℂ)) := hsl
          _ = ((D.r : ℚ) : ℂ) := hrC.symm
          _ = (D.lam : ℂ) * ((D.alpha1 : ℚ) : ℂ) := hlam_alpha1C.symm
      exact mul_left_cancel₀ hlam h
    refine ⟨P1Point.ofFinite D.alpha1, D.halpha1S, (gPoly D).eval D.alpha1, ?_, ?_⟩
    · rw [hzalpha1, aeval_cast_eval]
    · rfl

/-- Pointwise corollary in the form consumed by StepProviderStatement. -/
theorem critValueInImage (D : Mzk1ScaleData) (H : Lemma22Hypotheses D.S D.beta) (z : ℂ)
    (hz : aeval z (Polynomial.derivative (gPoly D)) = 0) :
    ∃ p ∈ D.S, ∃ v : ℚ, (v : ℂ) = aeval z (gPoly D) ∧
      polyEvalP1 (gPoly D) p = P1Point.ofFinite v :=
  critValueInImageStatement_proved D H z hz

/-! ## 4. Critical values for even n via the Belyi bridge -/

/-- For even n, c * gPoly(z) = B_{m,n}(lam * z); hence the critical values of gPoly are
the critical values of the canonical Belyi polynomial, scaled by c^{-1}. -/
theorem belyiNormConst_mul_aeval_gPoly (D : Mzk1ScaleData) (hne : Even D.n) (z : ℂ) :
    ((belyiNormConst D.m D.n : ℚ) : ℂ) * aeval z (gPoly D) =
      aeval ((D.lam : ℂ) * z) (belyiPolynomial ℚ D.m D.n) := by
  calc ((belyiNormConst D.m D.n : ℚ) : ℂ) * aeval z (gPoly D)
      = aeval z (C (belyiNormConst D.m D.n) * gPoly D) := by
        rw [Polynomial.aeval_mul, Polynomial.aeval_C]
        rfl
    _ = aeval z ((belyiPolynomial ℚ D.m D.n).comp (C D.lam * X)) := by
        rw [C_belyiNormConst_mul_gPoly_eq_comp D hne]
    _ = aeval ((D.lam : ℂ) * z) (belyiPolynomial ℚ D.m D.n) :=
        aeval_comp_C_mul_X _ _ _

/-- Critical values of gPoly over C (even n).  If z is critical then its value is
0 or (belyiNormConst m n)^{-1}. -/
theorem gPoly_critValue_normalized (D : Mzk1ScaleData) (hne : Even D.n) (z : ℂ)
    (hz : aeval z (Polynomial.derivative (gPoly D)) = 0) :
    ((belyiNormConst D.m D.n : ℚ) : ℂ) * aeval z (gPoly D) = 0 ∨
      ((belyiNormConst D.m D.n : ℚ) : ℂ) * aeval z (gPoly D) = 1 := by
  have hcomp := C_belyiNormConst_mul_gPoly_eq_comp D hne
  have hder : aeval z (derivative (C (belyiNormConst D.m D.n) * gPoly D)) = 0 := by
    rw [derivative_C_mul, Polynomial.aeval_mul, Polynomial.aeval_C, hz, mul_zero]
  rw [hcomp] at hder
  rw [aeval_derivative_comp_C_mul_X] at hder
  have hcrit : aeval ((D.lam : ℂ) * z) (derivative (belyiPolynomial ℚ D.m D.n)) = 0 := by
    rcases mul_eq_zero.mp hder with h | h
    · exact absurd h (lam_cast_ne_zero D)
    · exact h
  have hval := belyiPolynomial_critIn01 D.hm D.hn ((D.lam : ℂ) * z) hcrit
  rw [belyiNormConst_mul_aeval_gPoly D hne z]
  exact hval

/-- Critical values of gPoly over C (even n), solved form. -/
theorem gPoly_critValue_eq_zero_or_inv (D : Mzk1ScaleData) (hne : Even D.n) (z : ℂ)
    (hz : aeval z (Polynomial.derivative (gPoly D)) = 0) :
    aeval z (gPoly D) = 0 ∨
      aeval z (gPoly D) = (((belyiNormConst D.m D.n : ℚ) : ℂ))⁻¹ := by
  have hc : ((belyiNormConst D.m D.n : ℚ) : ℂ) ≠ 0 := by
    exact_mod_cast belyiNormConst_ne_zero D.m D.n
  rcases gPoly_critValue_normalized D hne z hz with h | h
  · exact Or.inl ((mul_eq_zero.mp h).resolve_left hc)
  · exact Or.inr (inv_eq_of_mul_eq_one_right h).symm

/-- Repaired 0/1 target (PROVED).  For the Belyi-normalized polynomial
belyiNormGPoly D = C c * gPoly D (which for even n equals B_{m,n}(lam * X)),
every C-point critical value is 0 or 1.  This is the true version of the literal target
requested for gPoly; the unnormalized gPoly does NOT satisfy it (see section 6). -/
def belyiNormGPoly (D : Mzk1ScaleData) : ℚ[X] :=
  C (belyiNormConst D.m D.n) * gPoly D

theorem belyiNormGPoly_critValue_zero_or_one (D : Mzk1ScaleData) (hne : Even D.n) (z : ℂ)
    (hz : aeval z (Polynomial.derivative (belyiNormGPoly D)) = 0) :
    aeval z (belyiNormGPoly D) = 0 ∨ aeval z (belyiNormGPoly D) = 1 := by
  have hc : ((belyiNormConst D.m D.n : ℚ) : ℂ) ≠ 0 := by
    exact_mod_cast belyiNormConst_ne_zero D.m D.n
  have hder : aeval z (Polynomial.derivative (gPoly D)) = 0 := by
    have h := hz
    unfold belyiNormGPoly at h
    rw [derivative_C_mul, Polynomial.aeval_mul, Polynomial.aeval_C] at h
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 hc
    · exact h0
  unfold belyiNormGPoly
  rw [Polynomial.aeval_mul, Polynomial.aeval_C]
  exact gPoly_critValue_normalized D hne z hder

/-! ## 5. The normalizing constant is not 1 -/

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

/-- The Belyi normalizing constant is never 1 (m, n >= 1). -/
theorem belyiNormConst_ne_one {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    belyiNormConst m n ≠ 1 := by
  have hlt := pow_mul_pow_lt_pow_add hm hn
  have hcast : ((m : ℚ) ^ m * (n : ℚ) ^ n) < (((m : ℚ) + n) ^ (m + n)) := by
    have h1 : (m : ℚ) ^ m * (n : ℚ) ^ n = ((m ^ m * n ^ n : ℕ) : ℚ) := by
      push_cast
      ring
    have h2 : ((m : ℚ) + n) ^ (m + n) = (((m + n) ^ (m + n) : ℕ) : ℚ) := by
      push_cast
      ring
    rw [h1, h2]
    exact_mod_cast hlt
  intro h
  have hden : ((m : ℚ) ^ m * (n : ℚ) ^ n) ≠ 0 := by positivity
  unfold belyiNormConst at h
  rw [div_eq_iff hden, one_mul] at h
  linarith

theorem belyiNormConst_inv_ne_one {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (((belyiNormConst m n : ℚ) : ℂ))⁻¹ ≠ 1 := by
  intro h
  have hcon : belyiNormConst m n = 1 := by
    have h1 : ((belyiNormConst m n : ℚ) : ℂ) = 1 := by
      calc ((belyiNormConst m n : ℚ) : ℂ)
          = ((((belyiNormConst m n : ℚ) : ℂ))⁻¹)⁻¹ := (inv_inv _).symm
        _ = 1 := by rw [h, inv_one]
    exact Rat.cast_injective (by simpa using h1)
  exact belyiNormConst_ne_one hm hn hcon

/-! ## 6. Refutation of the literal requested 0/1 target -/

/-- The explicit critical point z = (m/(m+n)) / lam. -/
def critPointZ (D : Mzk1ScaleData) : ℂ :=
  ((D.m : ℂ) / ((D.m : ℂ) + (D.n : ℂ))) / (D.lam : ℂ)

theorem lam_mul_critPointZ (D : Mzk1ScaleData) :
    (D.lam : ℂ) * critPointZ D = (D.m : ℂ) / ((D.m : ℂ) + (D.n : ℂ)) := by
  have hlam : (D.lam : ℂ) ≠ 0 := lam_cast_ne_zero D
  unfold critPointZ
  field_simp

theorem aeval_belyi21_at_div (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    aeval ((m : ℂ) / ((m : ℂ) + (n : ℂ))) (derivative (belyi21 m n)) = 0 := by
  rw [aeval_derivative_belyi21 m n hm hn]
  have hden : (m : ℂ) + (n : ℂ) ≠ 0 := by
    have hpos : ((m + n : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (by omega : m + n ≠ 0)
    simpa using hpos
  have hx : ((m + n : ℕ) : ℂ) * ((m : ℂ) / ((m : ℂ) + (n : ℂ))) - (m : ℂ) = 0 := by
    have hcast : ((m + n : ℕ) : ℂ) = (m : ℂ) + (n : ℂ) := by
      push_cast
      ring
    rw [hcast]
    field_simp
    ring
  rw [hx, mul_zero]

/-- The explicit critical point critPointZ D is a critical point of gPoly D. -/
theorem critPointZ_derivative_zero (D : Mzk1ScaleData) :
    aeval (critPointZ D) (Polynomial.derivative (gPoly D)) = 0 := by
  rw [aeval_derivative_gPoly_eq, lam_mul_critPointZ, aeval_belyi21_at_div D.m D.n D.hm D.hn,
    mul_zero]

/-- At the explicit critical point, c * gPoly(z) = 1 (the third Belyi critical value
of the normalized polynomial). -/
theorem belyiNormConst_mul_aeval_gPoly_at_critPointZ (D : Mzk1ScaleData) (hne : Even D.n) :
    ((belyiNormConst D.m D.n : ℚ) : ℂ) * aeval (critPointZ D) (gPoly D) = 1 := by
  rw [belyiNormConst_mul_aeval_gPoly D hne, lam_mul_critPointZ]
  have hcast : (D.m : ℂ) / ((D.m : ℂ) + (D.n : ℂ)) =
      (((D.m : ℚ) / ((D.m : ℚ) + (D.n : ℚ)) : ℚ) : ℂ) := by
    push_cast
    ring
  rw [hcast, aeval_cast_eval]
  have h1 : (belyiPolynomial ℚ D.m D.n).eval
      ((D.m : ℚ) / ((D.m : ℚ) + (D.n : ℚ))) = 1 := by
    simpa using (eval_div_belyiPolynomial (K := ℚ) D.m D.n)
  rw [h1]
  norm_num

/-- The literal requested target is false, for every D with Even D.n.  There is a
C-point critical point whose value is neither 0 nor 1. -/
theorem s3135_critValueInImage_counterexample (D : Mzk1ScaleData) (hne : Even D.n) :
    ∃ z : ℂ, aeval z (Polynomial.derivative (gPoly D)) = 0 ∧
      aeval z (gPoly D) ≠ 0 ∧ aeval z (gPoly D) ≠ 1 := by
  refine ⟨critPointZ D, critPointZ_derivative_zero D, ?_, ?_⟩
  · intro h0
    have h := belyiNormConst_mul_aeval_gPoly_at_critPointZ D hne
    rw [h0, mul_zero] at h
    norm_num at h
  · intro h1
    have h := belyiNormConst_mul_aeval_gPoly_at_critPointZ D hne
    rw [h1, mul_one] at h
    have hc1 : ((belyiNormConst D.m D.n : ℚ) : ℂ) = ((1 : ℚ) : ℂ) := by
      simpa using h
    exact belyiNormConst_ne_one D.hm D.hn (Rat.cast_injective hc1)

/-- The literal requested statement, for fixed (D, hne) (the exact target of the task). -/
def s3135CritValueInImageTargetAt (D : Mzk1ScaleData) (_hne : Even D.n) : Prop :=
  ∀ z : ℂ, aeval z (Polynomial.derivative (gPoly D)) = 0 →
    aeval z (gPoly D) = 0 ∨ aeval z (gPoly D) = 1

/-- REFUTED: the literal target fails for every (D, hne). -/
theorem s3135_critValueInImage_refuted (D : Mzk1ScaleData) (hne : Even D.n) :
    ¬ s3135CritValueInImageTargetAt D hne := by
  intro H
  obtain ⟨z, hz, h0, h1⟩ := s3135_critValueInImage_counterexample D hne
  rcases H z hz with h | h
  · exact h0 h
  · exact h1 h

/-! ## 7. Ledger and blocker -/

/-- Named blocker: the literal spec is false; it has to be replaced by
CritValueInImageStatement (PROVED here) or by the normalized version
belyiNormGPoly_critValue_zero_or_one (PROVED here). -/
def critValueInImageSpecBlocker : String :=
  "REQUESTED 0/1 TARGET IS FALSE for the unnormalized gPoly: the third critical value is " ++
  "(m^m*n^n)/(m+n)^(m+n) != 1. Use CritValueInImageStatement (PROVED: " ++
  "critValueInImageStatement_proved) or belyiNormGPoly_critValue_zero_or_one (PROVED)."

def critValueInImageProofRows : List (String × String × String) :=
  [ ("chain rule over C for gPoly (shift f0q killed by derivative)", "PROVED",
      "aeval_derivative_gPoly_eq (no even-n needed)")
  , ("true CV-in-image (paper Lemma 2.2(i))", "PROVED",
      "critValueInImageStatement_proved : CritValueInImageStatement")
  , ("gPoly critical values for even n", "PROVED",
      "gPoly_critValue_normalized / gPoly_critValue_eq_zero_or_inv")
  , ("normalized 0/1 statement via belyiPolynomial_critIn01", "PROVED",
      "belyiNormGPoly_critValue_zero_or_one")
  , ("belyi normalizing constant != 1", "PROVED",
      "pow_mul_pow_lt_pow_add / belyiNormConst_ne_one")
  , ("literal requested 0/1 target", "REFUTED (false)",
      "s3135_critValueInImage_counterexample / s3135_critValueInImage_refuted")
  , ("spec blocker", "OPEN (external)", critValueInImageSpecBlocker) ]

theorem critValueInImageProofRows_length : critValueInImageProofRows.length = 7 := rfl

#check critValueInImageStatement_proved
#check critValueInImage
#check gPoly_critValue_eq_zero_or_inv
#check belyiNormGPoly_critValue_zero_or_one
#check s3135_critValueInImage_counterexample
#check s3135_critValueInImage_refuted
#check critValueInImageProofRows_length

end LeanFormal.IUT.XiFPaper.Mzk1CritValueInImageProofActual
end
