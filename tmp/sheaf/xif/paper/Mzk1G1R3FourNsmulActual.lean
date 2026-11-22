/- R3 M2 (n=4) logical chain: `4 • P = 0 ↔ 2 • (2 • P) = 0 ↔ ψ₂(2P) = 0`,
  plus the Mathlib even-n identity `Ψ 4 = C (preΨ 4) * ψ₂`.

  RECON: `WeierstrassCurve.Ψ_eq_C_preΨ_mul_ψ₂_of_even`
  (EllipticDivisionPolynomialEvaluation.lean:133) and the n=2 criterion (M1).
  The remaining M2 input from henry is the coordinate formula
  `(2P).X = W.addX x x (W.slope x x y y)` and the identity
  `ψ₂(2P) = ψ₄(P)/ψ₂(P)^3` (equivalently the `x([2]P)` formula with `Φ 2`/`ΨSq 2`).
  No sorry/axiom. -/
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation
import tmp.sheaf.xif.paper.Mzk1G1R3TorsionCriterionActual
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R3FourNsmulActual
open LeanFormal.IUT

variable {A : Type*} [AddCommGroup A]

/-- `4 • P = 2 • (2 • P)`（zsmul 结合）。 -/
theorem four_nsmul_eq_two_nsmul_two_nsmul (P : A) :
    (4 : ℤ) • P = (2 : ℤ) • ((2 : ℤ) • P) := by
  rw [show (4 : ℤ) = 2 * 2 from by norm_num, mul_zsmul]

/-- `4 • P = 0 ↔ 2 • (2 • P) = 0`。 -/
theorem four_nsmul_eq_zero_iff_two_nsmul_two_nsmul_eq_zero (P : A) :
    (4 : ℤ) • P = 0 ↔ (2 : ℤ) • ((2 : ℤ) • P) = 0 := by
  rw [four_nsmul_eq_two_nsmul_two_nsmul]

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

/-- `Ψ 4 = C (preΨ 4) * ψ₂`（Mathlib even-n donor）。 -/
theorem Psi_four_eq : W.Ψ 4 = C (W.preΨ 4) * W.ψ₂ :=
  W.Ψ_eq_C_preΨ_mul_ψ₂_of_even (by decide : Even (4 : ℤ))

/-- **M2 链**：`4 • P = 0 ↔ ψ₂(2P) = 0`（`2•(2P)=0` 的 n=2 criterion）。 -/
theorem four_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_two_nsmul
    (P : W.toAffine.Point) :
    (4 : ℤ) • P = 0 ↔
      W.evalDivisionPolynomialAtPoint 2 ((2 : ℤ) • P) = 0 := by
  rw [four_nsmul_eq_zero_iff_two_nsmul_two_nsmul_eq_zero]
  rw [show (2 : ℤ) • ((2 : ℤ) • P) = (2 : ℕ) • ((2 : ℤ) • P) from natCast_zsmul _ 2]
  exact W.two_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_eq_zero _

#print axioms four_nsmul_eq_two_nsmul_two_nsmul
#print axioms four_nsmul_eq_zero_iff_two_nsmul_two_nsmul_eq_zero
#print axioms Psi_four_eq
#print axioms four_nsmul_eq_zero_iff_evalDivisionPolynomialAtPoint_two_two_nsmul

end LeanFormal.IUT.XiFPaper.Mzk1G1R3FourNsmulActual
