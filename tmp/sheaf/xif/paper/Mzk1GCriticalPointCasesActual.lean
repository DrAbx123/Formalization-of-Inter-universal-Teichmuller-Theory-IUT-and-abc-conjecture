import tmp.sheaf.xif.paper.Mzk1GDerivAevalActual
import tmp.sheaf.xif.paper.Mzk1Lemma22GChoiceConstructActual
import Mathlib.Tactic

/-! # Mzk1GCriticalPointCasesActual — C-critical points of gPoly lie among the rational scale-data points (stage4)

STEP 0 prior-art (reuse, no re-proof):
* Mzk1GDerivAevalActual: gPoly_deriv_aeval / gPoly_deriv_aeval_of_any_n (cast-form
  derivative-aeval formula over C), lam_cast_ne_zero, gPoly_deriv_aeval_eq_zero_iff,
  gPoly_deriv_aeval_zero_cases (C root dichotomy for Even n).
* Mzk1Lemma21Actual: belyi21, belyi21_derivative, belyi21_derivative_root (C root
  dichotomy 0 / 1 / (m+n)x = m for the Belyi polynomial).
* Mzk1Lemma22GChoiceConstructActual: Mzk1ScaleData (lam, alpha1, alpha2, m, n,
  hlam_alpha2, r_eq, hr_eq, lam_pos, ...), gPoly.
* Mzk1GChoiceUnramifiedActual: lam_mul_alpha1 (lam * alpha1 = r), lam_ne_zero'.
* Mzk1GChoiceCriticalInTargetActual: the same identification at the RATIONAL level
  (x : Q, gPoly_derivative_zero_cases); the present file is the C-point statement,
  z : C, for the polynomial derivative aeval z (derivative (gPoly D)).

DELIVERABLE (MAIN): for every D : Mzk1ScaleData and z : C,

  aeval z (derivative (gPoly D)) = 0  ->  z = 0 or z = (D.alpha2 : C) or z = (D.alpha1 : C).

Proof route (as planned): the evenness-free cast formula gPoly_deriv_aeval_of_any_n plus
lam != 0 gives that lam * z is a C-root of belyi21', hence lam * z in {0, 1, m/(m+n)}
(belyi21_derivative_root).  Dividing by lam != 0 in C:
* lam * z = 0 gives z = 0;
* lam * z = 1 and lam * alpha2 = 1 (cast of D.hlam_alpha2) give z = alpha2;
* (m+n) * (lam * z) = m gives lam * z = m/(m+n) = r (cast of D.hr_eq), and
  lam * alpha1 = r (cast of lam_mul_alpha1) gives z = alpha1 by cancellation of lam.
No sorry, no new axiom, no placeholder.  Even D.n is NOT needed: the even-n consumer
wrapper gPoly_critical_point_cases_of_even instead feeds gPoly_deriv_aeval_zero_cases
(Even n) into the case-elimination lemma critical_point_cases_of_dichotomy.

Remark (honest): the CONVERSE fails in general.  For m = 1 the point z = 0 is not
critical: f'(0) = (-1)^n != 0.  For n = 1 the point z = alpha2 is not critical:
f'(1) = 1 != 0 (reading (x-1)^0 = 1 in the derivative formula).  So the critical locus
is contained in {0, alpha2, alpha1}; equality of sets is not asserted. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GCriticalPointCasesActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1GDerivAevalActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21Actual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceUnramifiedActual

/-! ## 1. Cast-level scale-data identities -/

/-- Cast form of the scale-data identity lam * alpha2 = 1: in C the two rational
points alpha2 and 1/lam coincide. -/
theorem lam_mul_alpha2_cast (D : Mzk1ScaleData) :
    (D.lam : ℂ) * (D.alpha2 : ℂ) = 1 := by
  calc (D.lam : ℂ) * (D.alpha2 : ℂ) = ((D.lam * D.alpha2 : ℚ) : ℂ) := by
        push_cast
        ring
    _ = ((1 : ℚ) : ℂ) := by rw [D.hlam_alpha2]
    _ = 1 := by norm_num

/-- Cast form of D.hr_eq: r = m/(m+n) as complex numbers.  The rational identity is
obtained by casting the real identity D.hr_eq down to Q (CharZero). -/
theorem r_cast_eq (D : Mzk1ScaleData) :
    (D.r : ℂ) = (D.m : ℂ) / ((D.m + D.n : ℕ) : ℂ) := by
  have hrq : D.r = (D.m : ℚ) / ((D.m + D.n : ℕ) : ℚ) := by
    rw [D.r_eq]
    have h := D.hr_eq
    rw [D.r_eq] at h
    have hQ : ((D.alpha1 / D.alpha2 : ℚ) : ℝ) =
        (((D.m : ℚ) / ((D.m + D.n : ℕ) : ℚ)) : ℝ) := by
      rw [h]
      push_cast
      ring
    exact_mod_cast hQ
  rw [hrq]
  push_cast
  ring

/-! ## 2. The evenness-free C-point root dichotomy for gPoly -/

/-- **C-point root dichotomy (evenness-free):** a C-critical point z of gPoly has
lam * z in {0, 1, m/(m+n)} (the last in the affine form ((m+n) : C) * (lam * z) = m).
Derived from gPoly_deriv_aeval_of_any_n, lam_cast_ne_zero and belyi21_derivative_root;
unlike gPoly_deriv_aeval_zero_cases no Even D.n is required. -/
theorem gPoly_deriv_aeval_zero_cases_any_n (D : Mzk1ScaleData) {z : ℂ}
    (h : Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0) :
    (D.lam : ℂ) * z = 0 ∨ (D.lam : ℂ) * z = 1 ∨
      ((D.m + D.n : ℕ) : ℂ) * ((D.lam : ℂ) * z) = (D.m : ℂ) := by
  have hlam : (D.lam : ℂ) ≠ 0 := lam_cast_ne_zero D
  have h0 : Polynomial.aeval ((D.lam : ℂ) * z)
      (Polynomial.derivative (belyi21 D.m D.n)) = 0 := by
    have h' : (D.lam : ℂ) * Polynomial.aeval ((D.lam : ℂ) * z)
        (Polynomial.derivative (belyi21 D.m D.n)) = 0 := by
      rw [← gPoly_deriv_aeval_of_any_n D z]
      exact h
    rcases mul_eq_zero.mp h' with h' | h'
    · exact absurd h' hlam
    · exact h'
  exact belyi21_derivative_root D.hm D.hn h0

/-! ## 3. Main theorem: C-critical points of gPoly -/

/-- **Case elimination:** if lam * z is 0, 1, or m/(m+n) (the last in the affine form
((m+n) : C) * (lam * z) = m), then z is one of the scale-data points 0, alpha2, alpha1.
Pure field algebra over C: cancel lam != 0, and use the cast identities
lam * alpha2 = 1 (D.hlam_alpha2) and lam * alpha1 = r = m/(m+n) (lam_mul_alpha1, D.hr_eq). -/
theorem critical_point_cases_of_dichotomy (D : Mzk1ScaleData) {z : ℂ}
    (h : (D.lam : ℂ) * z = 0 ∨ (D.lam : ℂ) * z = 1 ∨
      ((D.m + D.n : ℕ) : ℂ) * ((D.lam : ℂ) * z) = (D.m : ℂ)) :
    z = 0 ∨ z = (D.alpha2 : ℂ) ∨ z = (D.alpha1 : ℂ) := by
  have hlam : (D.lam : ℂ) ≠ 0 := lam_cast_ne_zero D
  have hA2 : (D.lam : ℂ) * (D.alpha2 : ℂ) = 1 := lam_mul_alpha2_cast D
  rcases h with h0 | h1 | h3
  · left
    rcases mul_eq_zero.mp h0 with h' | h'
    · exact absurd h' hlam
    · exact h'
  · right; left
    calc z = z * ((D.lam : ℂ) * (D.alpha2 : ℂ)) := by rw [hA2, mul_one]
      _ = ((D.lam : ℂ) * z) * (D.alpha2 : ℂ) := by ring
      _ = 1 * (D.alpha2 : ℂ) := by rw [h1]
      _ = (D.alpha2 : ℂ) := by ring
  · right; right
    have hmn : ((D.m + D.n : ℕ) : ℂ) ≠ 0 := by
      have hpos : (0 : ℕ) < D.m + D.n :=
        Nat.add_pos_left (Nat.zero_lt_one.trans_le D.hm) D.n
      exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hpos)
    have hzr : (D.lam : ℂ) * z = (D.r : ℂ) := by
      have hsl : (D.lam : ℂ) * z = (D.m : ℂ) / ((D.m + D.n : ℕ) : ℂ) := by
        rw [eq_div_iff hmn, mul_comm ((D.lam : ℂ) * z) (((D.m + D.n : ℕ)) : ℂ)]
        exact h3
      rw [hsl, ← r_cast_eq D]
    have halpha1 : (D.lam : ℂ) * (D.alpha1 : ℂ) = (D.r : ℂ) := by
      calc (D.lam : ℂ) * (D.alpha1 : ℂ) = ((D.lam * D.alpha1 : ℚ) : ℂ) := by
            push_cast
            ring
        _ = (D.r : ℂ) := by rw [lam_mul_alpha1 D]
    exact mul_left_cancel₀ hlam (by rw [hzr, halpha1])

/-- **MAIN (stage4):** every C-critical point of the g-choice polynomial is one of the
rational scale-data points 0, alpha2, alpha1 (read in C).  Evenness-free route through
gPoly_deriv_aeval_zero_cases_any_n; the even-n consumer form is
gPoly_critical_point_cases_of_even below. -/
theorem gPoly_critical_point_cases (D : Mzk1ScaleData) {z : ℂ}
    (h : Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0) :
    z = 0 ∨ z = (D.alpha2 : ℂ) ∨ z = (D.alpha1 : ℂ) :=
  critical_point_cases_of_dichotomy D (gPoly_deriv_aeval_zero_cases_any_n D h)

/-- **Even-n consumer wrapper (the dichotomy named in the stage4 route):** same conclusion
from gPoly_deriv_aeval_zero_cases of Mzk1GDerivAevalActual, which requires Even D.n. -/
theorem gPoly_critical_point_cases_of_even (D : Mzk1ScaleData) (hne : Even D.n) {z : ℂ}
    (h : Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0) :
    z = 0 ∨ z = (D.alpha2 : ℂ) ∨ z = (D.alpha1 : ℂ) :=
  critical_point_cases_of_dichotomy D (gPoly_deriv_aeval_zero_cases D hne h)

/-- **Off-point contrapositive:** a C-point different from 0, alpha2, alpha1 is not a
critical point of gPoly.  This is the form consumed by unramifiedness arguments. -/
theorem gPoly_deriv_aeval_ne_zero_of_ne (D : Mzk1ScaleData) {z : ℂ}
    (h0 : z ≠ 0) (h2 : z ≠ (D.alpha2 : ℂ)) (h1 : z ≠ (D.alpha1 : ℂ)) :
    Polynomial.aeval z (Polynomial.derivative (gPoly D)) ≠ 0 := by
  intro h
  rcases gPoly_critical_point_cases D h with h' | h' | h'
  · exact h0 h'
  · exact h2 h'
  · exact h1 h'

/-- **Set form:** the C-critical locus of gPoly is contained in {0, alpha2, alpha1}. -/
theorem gPoly_critical_points_subset (D : Mzk1ScaleData) :
    {z : ℂ | Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0} ⊆
      ({0, (D.alpha2 : ℂ), (D.alpha1 : ℂ)} : Set ℂ) := by
  intro z hz
  rcases gPoly_critical_point_cases D hz with h | h | h <;> simp [h]

/-! ## 4. Row ledger -/

structure GCriticalPointRow where
  item : String
  status : String
  proved : Bool

def gCriticalPointRows : List GCriticalPointRow :=
  [ ⟨"cast form lam * alpha2 = 1 over C", "PROVED (lam_mul_alpha2_cast)", true⟩,
    ⟨"cast form r = m/(m+n) over C", "PROVED (r_cast_eq, from D.hr_eq via D.r_eq)", true⟩,
    ⟨"evenness-free C root dichotomy: lam*z in {0, 1, m/(m+n)}", "PROVED (gPoly_deriv_aeval_zero_cases_any_n)", true⟩,
    ⟨"case elimination from the dichotomy (lam*z in {0,1,m/(m+n)} -> z in {0, alpha2, alpha1})", "PROVED (critical_point_cases_of_dichotomy)", true⟩,
    ⟨"C-critical points of gPoly are 0 / alpha2 / alpha1", "PROVED (gPoly_critical_point_cases); even-n wrapper gPoly_critical_point_cases_of_even", true⟩,
    ⟨"off-point contrapositive: derivative nonzero away from 0 / alpha2 / alpha1", "PROVED (gPoly_deriv_aeval_ne_zero_of_ne)", true⟩,
    ⟨"subset form of the critical locus", "PROVED (gPoly_critical_points_subset)", true⟩,
    ⟨"converse: 0 / alpha2 / alpha1 are critical points", "NOT CLAIMED (false for m = 1 resp. n = 1; see file header)", false⟩ ]

theorem gCriticalPointRows_length : gCriticalPointRows.length = 8 := rfl

#check lam_mul_alpha2_cast
#check r_cast_eq
#check gPoly_deriv_aeval_zero_cases_any_n
#check critical_point_cases_of_dichotomy
#check gPoly_critical_point_cases
#check gPoly_critical_point_cases_of_even
#check gPoly_deriv_aeval_ne_zero_of_ne
#check gPoly_critical_points_subset
#check gCriticalPointRows_length

#print axioms gPoly_critical_point_cases
#print axioms gPoly_critical_point_cases_of_even
#print axioms gPoly_deriv_aeval_zero_cases_any_n
#print axioms gPoly_critical_points_subset

end LeanFormal.IUT.XiFPaper.Mzk1GCriticalPointCasesActual
end
