import tmp.sheaf.xif.paper.Mzk1G1ABCCompactnessActual
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1Actual
open Polynomial

/-- Actual Frey curve coefficients for a+b=c: y^2=x(x-a)(x+b). -/
def freyA (a b : ℕ) : ℤ := (b : ℤ) - (a : ℤ)
def freyB (a b : ℕ) : ℤ := -((a : ℤ) * (b : ℤ))

/-- Actual Frey curve polynomial. -/
def freyPolynomial (a b c : ℕ) : ℤ[X] :=
  X ^ 3 + C (freyA a b) * X ^ 2 + C (freyB a b) * X

/-- Actual Frey discriminant Δ = 16 a^2 b^2 c^2 for c=a+b. -/
def freyDiscriminant (a b c : ℕ) : ℤ :=
  16 * (a : ℤ) ^ 2 * (b : ℤ) ^ 2 * (c : ℤ) ^ 2

/-- Actual Frey conductor: radical of abc. -/
def freyConductor (a b c : ℕ) : ℕ := radical (a * b * c)

theorem freyDiscriminant_ne_zero (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    freyDiscriminant a b c ≠ 0 := by
  unfold freyDiscriminant
  positivity

theorem freyConductor_eq_radical (a b c : ℕ) :
    freyConductor a b c = radical (a * b * c) := rfl

/-- Actual ABC elliptic-height criterion of §13.3, phrased with the Frey
discriminant and conductor. -/
structure ABCEllipticHeightCriterion (ε : ℝ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  frey_discriminant_nonzero :
    ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → a + b = c →
      freyDiscriminant a b c ≠ 0
  height_ineq :
    ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → a + b = c →
      Nat.Coprime a b →
      (c : ℝ) ≤ C * (freyConductor a b c : ℝ) ^ (1 + ε)

/-- Actual criterion for every ε>0. -/
def ABCEllipticHeightCriterionAll : Prop :=
  ∀ ε : ℝ, 0 < ε → Nonempty (ABCEllipticHeightCriterion ε)

/-- Actual consumer: the elliptic-height criterion implies ABCStatement. -/
theorem abcStatement_of_ellipticHeightCriterion
    (h : ABCEllipticHeightCriterionAll) : ABCStatement := by
  intro ε hε
  rcases h ε hε with ⟨D⟩
  refine ⟨D.C, D.C_nonneg, ?_⟩
  intro a b c ha hb hc hab hcop
  have hbound := D.height_ineq a b c ha hb hc hab hcop
  simpa [freyConductor] using hbound

end LeanFormal.IUT.XiFPaper.Mzk1G1Actual
end
