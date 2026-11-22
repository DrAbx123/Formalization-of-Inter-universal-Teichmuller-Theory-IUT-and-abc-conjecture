import tmp.sheaf.xif.paper.AG02FunctionFieldActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# AG02b: principal divisor of a rational function (AG infrastructure, first layer)

A Weil divisor is represented by integer coefficients on codimension-one points.
For the first compileable layer we allow infinite support (function
AGCodimOnePoint X → ℤ); the finite-support refinement is a separate later layer
for proper smooth curves (Riemann-Roch prerequisite).

The principal divisor of a rational function f is the coefficient map
z ↦ ord_z(f), using Mathlib's Scheme.ord (reused, no re-proof).

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.AG02bPrincipalDivisorActual

open AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.AG02FunctionFieldActual

universe u

/-- A (first-layer) Weil divisor: integer coefficients on codimension-one points. -/
abbrev WeilDivisor (X : Scheme.{u}) : Type u := AGCodimOnePoint X → ℤ

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The coefficient of a divisor at a codimension-one point. -/
def weilDivisorCoeff (D : WeilDivisor X) (z : AGCodimOnePoint X) : ℤ := D z

/-- The zero divisor. -/
def weilDivisorZero : WeilDivisor X := 0

/-- Divisors form an additive commutative group by pointwise addition. -/
example : AddCommGroup (WeilDivisor X) := inferInstance

/-- Addition of divisors is pointwise. -/
theorem weilDivisor_add_apply (D E : WeilDivisor X) (z : AGCodimOnePoint X) :
    weilDivisorCoeff (D + E) z = weilDivisorCoeff D z + weilDivisorCoeff E z :=
  rfl

/-- The support of a divisor. -/
def weilDivisorSupport (D : WeilDivisor X) : Set (AGCodimOnePoint X) :=
  {z | D z ≠ 0}

/-- The zero divisor has empty support. -/
theorem weilDivisorSupport_zero : weilDivisorSupport (0 : WeilDivisor X) = ∅ := by
  ext z
  simp [weilDivisorSupport]

/-- The principal divisor of a rational function: coefficient ord_z(f). -/
def principalDivisor (f : X.functionField) : WeilDivisor X :=
  fun z => agOrderOfVanishing f z

/-- The principal divisor of the zero function is zero. -/
@[simp]
theorem principalDivisor_zero : principalDivisor (0 : X.functionField) = 0 := by
  funext z
  simp [principalDivisor]

/-- Principal divisors of nonzero functions are additive on products
(valution multiplicativity, reused Mathlib ord_mul). -/
theorem principalDivisor_mul {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    principalDivisor (f * g) = principalDivisor f + principalDivisor g := by
  funext z
  simp [principalDivisor, Pi.add_apply, agOrderOfVanishing_mul hf hg z]

/-- The coefficient of a principal divisor at a point. -/
theorem principalDivisor_coeff (f : X.functionField) (z : AGCodimOnePoint X) :
    weilDivisorCoeff (principalDivisor f) z = agOrderOfVanishing f z := rfl

end LeanFormal.IUT.XiFPaper.AG02bPrincipalDivisorActual

end
