import tmp.sheaf.xif.paper.Mzk1HTF4OrbitProductActual
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
/-!
# F4 divisor-height layer: weighted heights on reduced/multiplicity Weil divisors

Route §8.3 uses the height of `div(P|_Y)`.  This file provides the **algebraic divisor
height layer**: for a finite point type `X` and a local weight `h : X → ℝ`,
`divisorHeight h D = ∑ x, D(x) * h x` (`D(x)` is the integer coefficient).
* additivity `divisorHeight h (D+E) = divisorHeight h D + divisorHeight h E`;
* point divisors: `divisorHeight h (ofPoint x) = h x`;
* the reduced zero divisor `divP` of an orbit product is a sum of point divisors, so its
  height is the sum of `h` over `P = 0`;
* supports the multiplicity form `∑ x, ord x • ofPoint x` (explicit `ord` data).

## Reuse / donor check (2026-11-17)
* ported `TauCeti/AlgebraicGeometry/WeilDivisor/Basic` (`ofPoint`, `coeff`, `IsEffective`);
* `Mzk1HTF4OrbitProductActual` DONE 12:54:03 (`divP`/`Ediv`/`Fdiv`).

**Explicit obligation**: the identification of this algebraic `divisorHeight` with the
scheme/Arakelov divisor height (and with `Height.logHeight` on polynomial values) is not
proved here; the local multiplicity `ord x` (order of vanishing at `x`) is explicit data.
F4 is not closed until these are supplied.
-/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.HTF4DivisorHeightActual
open LeanFormal.IUT.XiFPaper.HTF4OrbitProductActual
open TauCeti.AlgebraicGeometry

variable {ι X : Type*} [Fintype ι] [Fintype X] [DecidableEq X]

/-- Algebraic height of a Weil divisor with respect to a local weight `h`. -/
def divisorHeight (h : X → ℝ) (D : WeilDivisor X) : ℝ :=
  ∑ x : X, (D x : ℝ) * h x

theorem divisorHeight_zero (h : X → ℝ) : divisorHeight h (0 : WeilDivisor X) = 0 := by
  simp [divisorHeight]

theorem divisorHeight_add (h : X → ℝ) (D E : WeilDivisor X) :
    divisorHeight h (D + E) = divisorHeight h D + divisorHeight h E := by
  simp [divisorHeight, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]

theorem divisorHeight_ofPoint (h : X → ℝ) (x : X) :
    divisorHeight h (WeilDivisor.ofPoint x) = h x := by
  classical
  simp [divisorHeight, WeilDivisor.ofPoint, Finsupp.single_apply]

theorem divisorHeight_neg (h : X → ℝ) (D : WeilDivisor X) :
    divisorHeight h (-D) = -divisorHeight h D := by
  simp [divisorHeight, Finsupp.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem divisorHeight_sub (h : X → ℝ) (D E : WeilDivisor X) :
    divisorHeight h (D - E) = divisorHeight h D - divisorHeight h E := by
  simp [divisorHeight, Finsupp.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- Additivity over finite sums of divisors. -/
theorem divisorHeight_sum (h : X → ℝ) (s : Finset X) (f : X → WeilDivisor X) :
    divisorHeight h (∑ x ∈ s, f x) = ∑ x ∈ s, divisorHeight h (f x) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [divisorHeight_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, divisorHeight_add, ih]

/-- Height of the reduced zero divisor `divP` (sum of point divisors). -/
theorem divisorHeight_divP (D : OrbitProductData ι X) (h : X → ℝ) :
    divisorHeight h D.divP =
      ∑ x ∈ (Finset.univ.filter (fun x => MvPolynomial.eval (D.eval x) D.P = 0)), h x := by
  classical
  simp [divisorHeight_sum, OrbitProductData.divP, divisorHeight_ofPoint]

#print axioms divisorHeight_add
#print axioms divisorHeight_ofPoint
#print axioms divisorHeight_divP
end LeanFormal.IUT.XiFPaper.HTF4DivisorHeightActual
end