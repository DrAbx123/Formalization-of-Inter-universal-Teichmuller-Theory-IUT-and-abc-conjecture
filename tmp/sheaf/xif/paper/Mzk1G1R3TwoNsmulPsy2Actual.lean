/- R3 milestone M2 bridge (Lead 01:xx ruling): the ONLY needed relation is the ZERO
equivalence `ψ₂(2P) = 0 ↔ preΨ₄(P) = 0` (then `4P = 0 ↔ ψ₂(2P) = 0 ↔ ψ₄(P) = 0`).
Here we provide the exact expansion of `ψ₂(2P) = 2·Y₂ + a₁·X₂ + a₃` in terms of
Mathlib's `addX`/`addY`/`slope`; clearing denominators and matching `preΨ₄` is the next step.
REUSE: `Mzk1G1R3TwoNsmulXActual.two_nsmul_some_x`,
`Mzk1G1R3TwoNsmulYActual.{two_nsmul_slope_eq, two_nsmul_addY_eq}`,
`WeierstrassCurve.Affine.{addX, addY, negY, negAddY}`,
`DivisionPolynomial.Basic.{preΨ, preΨ_four, Ψ₂Sq}`.
-/
import tmp.sheaf.xif.paper.Mzk1G1R3TwoNsmulYActual
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.Tactic

noncomputable section
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R3TwoNsmulPsy2Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1R3TwoNsmulXActual
open LeanFormal.IUT.XiFPaper.Mzk1G1R3TwoNsmulYActual

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F)

/-- `ψ₂` at the double `2 • (x, y)`: `2·Y₂ + a₁·X₂ + a₃` with `X₂ = addX`, `Y₂ = addY`. -/
def psi2AtTwo (x y : F) : F :=
  2 * W.addY x x y (W.slope x x y y) + W.a₁ * W.addX x x (W.slope x x y y) + W.a₃

/-- Exact expansion of `ψ₂(2P)` through the doubling slope. -/
theorem psi2AtTwo_eq {x y : F} (hy : y ≠ W.negY x y) :
    psi2AtTwo W x y = 
      -2 * (W.slope x x y y * (W.addX x x (W.slope x x y y) - x) + y)
        - W.a₁ * W.addX x x (W.slope x x y y) - W.a₃ :=
by
  unfold psi2AtTwo
  rw [two_nsmul_addY_eq W hy]
  ring

/-- `ψ₂` of the double in terms of the doubling slope and `addX` alone. -/
theorem psi2AtTwo_eq_slope {x y : F} (hy : y ≠ W.negY x y) :
    psi2AtTwo W x y =
      -2 * (W.slope x x y y * (W.addX x x (W.slope x x y y) - x) + y)
        - W.a₁ * W.addX x x (W.slope x x y y) - W.a₃ :=
  psi2AtTwo_eq W hy

#print axioms psi2AtTwo_eq
end LeanFormal.IUT.XiFPaper.Mzk1G1R3TwoNsmulPsy2Actual
