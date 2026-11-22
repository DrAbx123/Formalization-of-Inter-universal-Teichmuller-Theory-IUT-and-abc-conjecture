import tmp.sheaf.xif.paper.Mzk1BelyiCvBridgeActual
import tmp.sheaf.xif.paper.Mzk1GChoiceUnramifiedActual
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic

/-! # Mzk1GDerivAevalActual — cast-form derivative-aeval formula for gPoly (stage4)

STEP 0 prior-art: Mzk1BelyiCvBridgeActual (gPoly_eq_belyi21_comp PROVED: for Even n,
gPoly = belyi21.comp (C lam * X)); Mzk1Lemma22GChoiceConstructActual (gPoly, fq, f0q,
belyi21); Mzk1GChoiceUnramifiedActual (gPoly_derivative_eval over Q PROVED,
lam_mul_alpha1); Mzk1Lemma21Actual (belyi21_derivative_root over C PROVED);
Mzk1Lemma22CritValueActual (named row "derivative-aeval formula for gPoly over C");
Mathlib AlgebraMap/Derivative (derivative_comp, derivative_C_mul_X, aeval_comp,
aeval_mul, aeval_C, aeval_X, aeval_algebraMap_apply_eq_algebraMap_eval) -> REUSE.

Deliverable: the cast-form derivative-aeval formula requested by stage4,

  aeval z (derivative (gPoly D)) = (D.lam : C) * aeval ((D.lam : C) * z)
    (derivative (belyi21 D.m D.n)),      (z : C),

PROVED (theorem gPoly_deriv_aeval).  Proof: g = belyi21(lam * X) over Q (asset
gPoly_eq_belyi21_comp, uses Even n), chain rule derivative_comp + derivative_C_mul_X,
then the algebra-hom rules aeval_mul / aeval_comp / aeval_C / aeval_X.

Remarks (honest):
* The evenness hypothesis is used only through gPoly_eq_belyi21_comp; the identity
  itself does not need it, since the derivative kills the added constant f0q.  The
  evenness-free forms derivative_gPoly_eq / gPoly_deriv_aeval_of_any_n are also proved.
* Consequences proved here for stage4: gPoly_deriv_aeval_cast (consistency with the
  Q-level gPoly_derivative_eval), gPoly_deriv_aeval_eq_zero_iff, and the C-point root
  dichotomy gPoly_deriv_aeval_zero_cases (lam * z in {0, 1, m/(m+n)}).
* Still NAMED (not proved here, next stage4 row): the identification of those C-points
  with the rational points 0, alpha2, alpha1 of the scale data.
No sorry, no new axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1GDerivAevalActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma21Actual
open LeanFormal.IUT.XiFPaper.Mzk1BelyiCvBridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceUnramifiedActual

/-! ## 1. The polynomial identity behind the formula -/

/-- **Derivative shape of gPoly (evenness-free):** the derivative of the g-choice
polynomial is lambda times the derivative of belyi21 reparametrised by lambda * X.
The constant shift f0q differentiates away. -/
theorem derivative_gPoly_eq (D : Mzk1ScaleData) :
    Polynomial.derivative (gPoly D) =
      Polynomial.C D.lam *
        (Polynomial.derivative (belyi21 D.m D.n)).comp
          (Polynomial.C D.lam * Polynomial.X) := by
  unfold gPoly
  rw [Polynomial.derivative_add, Polynomial.derivative_C, add_zero]
  have hB : ((Polynomial.X : ℚ[X]) ^ D.m * ((Polynomial.X : ℚ[X]) - 1) ^ D.n) =
      belyi21 D.m D.n := rfl
  rw [hB, Polynomial.derivative_comp, Polynomial.derivative_C_mul_X]

/-- **Derivative shape of gPoly via the even-n asset:** for Even n, gPoly is the
Belyi polynomial precomposed with lambda * X, so the chain rule gives the same shape. -/
theorem derivative_gPoly_eq_of_even (D : Mzk1ScaleData) (hne : Even D.n) :
    Polynomial.derivative (gPoly D) =
      Polynomial.C D.lam *
        (Polynomial.derivative (belyi21 D.m D.n)).comp
          (Polynomial.C D.lam * Polynomial.X) := by
  rw [gPoly_eq_belyi21_comp D hne, Polynomial.derivative_comp, Polynomial.derivative_C_mul_X]

/-! ## 2. The cast-form derivative-aeval formula -/

/-- **MAIN (stage4):** cast-form derivative-aeval formula for the g-choice polynomial.
For every z : C, aeval of gPoly' at z is lambda times aeval of the Belyi derivative at
lambda * z.  Uses the even-n asset gPoly_eq_belyi21_comp. -/
theorem gPoly_deriv_aeval (D : Mzk1ScaleData) (hne : Even D.n) (z : ℂ) :
    Polynomial.aeval z (Polynomial.derivative (gPoly D)) =
      (D.lam : ℂ) * Polynomial.aeval ((D.lam : ℂ) * z)
        (Polynomial.derivative (belyi21 D.m D.n)) := by
  have hC : Polynomial.aeval z (Polynomial.C D.lam) = (D.lam : ℂ) := by
    rw [Polynomial.aeval_C]
    rfl
  have hX : Polynomial.aeval z (Polynomial.C D.lam * Polynomial.X) = (D.lam : ℂ) * z := by
    rw [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    rfl
  rw [derivative_gPoly_eq_of_even D hne, Polynomial.aeval_mul, hC, Polynomial.aeval_comp, hX]

/-- **Evenness-free form** of the cast-form derivative-aeval formula: the identity does
not need Even n (the added constant f0q differentiates away). -/
theorem gPoly_deriv_aeval_of_any_n (D : Mzk1ScaleData) (z : ℂ) :
    Polynomial.aeval z (Polynomial.derivative (gPoly D)) =
      (D.lam : ℂ) * Polynomial.aeval ((D.lam : ℂ) * z)
        (Polynomial.derivative (belyi21 D.m D.n)) := by
  have hC : Polynomial.aeval z (Polynomial.C D.lam) = (D.lam : ℂ) := by
    rw [Polynomial.aeval_C]
    rfl
  have hX : Polynomial.aeval z (Polynomial.C D.lam * Polynomial.X) = (D.lam : ℂ) * z := by
    rw [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    rfl
  rw [derivative_gPoly_eq D, Polynomial.aeval_mul, hC, Polynomial.aeval_comp, hX]

/-! ## 3. Consistency and consequences for stage4 -/

/-- **Consistency check with the Q-level formula:** at a cast rational point, the C-form
agrees with gPoly_derivative_eval (Mzk1GChoiceUnramifiedActual). -/
theorem gPoly_deriv_aeval_cast (D : Mzk1ScaleData) (x : ℚ) :
    Polynomial.aeval ((x : ℚ) : ℂ) (Polynomial.derivative (gPoly D)) =
      ((D.lam * (Polynomial.derivative (belyi21 D.m D.n)).eval (D.lam * x) : ℚ) : ℂ) := by
  have hcast : ((x : ℚ) : ℂ) = algebraMap ℚ ℂ x := rfl
  rw [hcast, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, gPoly_derivative_eval]
  rfl

/-- The cast of lambda is nonzero in C. -/
theorem lam_cast_ne_zero (D : Mzk1ScaleData) : (D.lam : ℂ) ≠ 0 := by
  rw [Rat.cast_ne_zero]
  exact ne_of_gt D.lam_pos

/-- **Critical-point equation over C:** z is a critical point of gPoly over C iff
lambda * z is a critical point of the Belyi polynomial over C. -/
theorem gPoly_deriv_aeval_eq_zero_iff (D : Mzk1ScaleData) (hne : Even D.n) (z : ℂ) :
    Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0 ↔
      Polynomial.aeval ((D.lam : ℂ) * z)
        (Polynomial.derivative (belyi21 D.m D.n)) = 0 := by
  constructor
  · intro h
    have h' : (D.lam : ℂ) * Polynomial.aeval ((D.lam : ℂ) * z)
        (Polynomial.derivative (belyi21 D.m D.n)) = 0 := by
      rw [← gPoly_deriv_aeval D hne z]
      exact h
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact absurd h0 (lam_cast_ne_zero D)
    · exact h0
  · intro h
    rw [gPoly_deriv_aeval D hne z, h, mul_zero]

/-- **Root dichotomy over C for gPoly (stage4 use):** if z : C is a critical point of
gPoly, then lambda * z is 0, 1, or m/(m+n) (in the form ((m+n) : C) * (lambda * z) = m).
Obtained from the cast formula and belyi21_derivative_root over C. -/
theorem gPoly_deriv_aeval_zero_cases (D : Mzk1ScaleData) (hne : Even D.n) {z : ℂ}
    (h : Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0) :
    (D.lam : ℂ) * z = 0 ∨ (D.lam : ℂ) * z = 1 ∨
      ((D.m + D.n : ℕ) : ℂ) * ((D.lam : ℂ) * z) = (D.m : ℂ) :=
  belyi21_derivative_root D.hm D.hn ((gPoly_deriv_aeval_eq_zero_iff D hne z).mp h)

/-! ## 4. Row ledger -/

structure GDerivAevalRow where
  item : String
  status : String
  proved : Bool

def gDerivAevalRows : List GDerivAevalRow :=
  [ ⟨"derivative shape of gPoly (evenness-free)", "PROVED (derivative_gPoly_eq)", true⟩,
    ⟨"derivative shape via even-n comp asset", "PROVED (derivative_gPoly_eq_of_even, uses gPoly_eq_belyi21_comp)", true⟩,
    ⟨"cast-form derivative-aeval formula aeval z g' = lam * aeval (lam z) f'", "PROVED (gPoly_deriv_aeval; evenness-free form gPoly_deriv_aeval_of_any_n)", true⟩,
    ⟨"consistency with Q-level gPoly_derivative_eval at cast rationals", "PROVED (gPoly_deriv_aeval_cast)", true⟩,
    ⟨"critical-point equation over C (iff, lambda nonzero)", "PROVED (gPoly_deriv_aeval_eq_zero_iff, lam_cast_ne_zero)", true⟩,
    ⟨"root dichotomy over C: lam * z in {0, 1, m/(m+n)}", "PROVED (gPoly_deriv_aeval_zero_cases)", true⟩,
    ⟨"identification of C-critical points with rational 0 / alpha2 / alpha1", "PENDING (named next stage4 row: divide by lam in C and match casts of alpha1/alpha2; out of scope of this package)", false⟩ ]

theorem gDerivAevalRows_length : gDerivAevalRows.length = 7 := rfl

#check derivative_gPoly_eq
#check derivative_gPoly_eq_of_even
#check gPoly_deriv_aeval
#check gPoly_deriv_aeval_of_any_n
#check gPoly_deriv_aeval_cast
#check lam_cast_ne_zero
#check gPoly_deriv_aeval_eq_zero_iff
#check gPoly_deriv_aeval_zero_cases
#check gDerivAevalRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GDerivAevalActual
end
