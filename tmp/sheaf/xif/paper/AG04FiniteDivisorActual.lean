import tmp.sheaf.xif.paper.AG03DivisorsSectionsActual
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# AG04: finite-support Weil divisors and their degree (AG infrastructure, second layer)

A finite-support Weil divisor (the actual Riemann-Roch object on a smooth proper
curve) as a finitely-supported integer coefficient family on codimension-one
points, with its degree and the embedding into the first-layer function-space
divisors of AG02b.  The finiteness of supports of principal divisors on a proper
smooth curve is postponed honestly (it is a Riemann-Roch prerequisite).

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.AG04FiniteDivisorActual

open AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.AG02FunctionFieldActual
open LeanFormal.IUT.XiFPaper.AG02bPrincipalDivisorActual
open LeanFormal.IUT.XiFPaper.AG03DivisorsSectionsActual

universe u

/-- A finite-support Weil divisor: finitely supported integer coefficients on
codimension-one points. -/
abbrev WeilDivisorFinite (X : Scheme.{u}) : Type u := AGCodimOnePoint X →₀ ℤ

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- The first-layer (function-space) divisor underlying a finite-support divisor. -/
def toWeilDivisor (E : WeilDivisorFinite X) : WeilDivisor X :=
  fun z => E z

/-- The underlying function of a finite-support divisor is its coefficient map. -/
theorem toWeilDivisor_apply (E : WeilDivisorFinite X) (z : AGCodimOnePoint X) :
    toWeilDivisor E z = E z := rfl

/-- The degree of a finite-support Weil divisor: the sum of its coefficients. -/
def weilDivisorFiniteDegree (E : WeilDivisorFinite X) : ℤ :=
  E.sum fun _ c => c

/-- The zero divisor has degree zero. -/
@[simp]
theorem weilDivisorFiniteDegree_zero :
    weilDivisorFiniteDegree (0 : WeilDivisorFinite X) = 0 := by
  simp [weilDivisorFiniteDegree]

/-- Degree is additive on finite-support divisors. -/
theorem weilDivisorFiniteDegree_add (E F : WeilDivisorFinite X) :
    weilDivisorFiniteDegree (E + F) = weilDivisorFiniteDegree E + weilDivisorFiniteDegree F := by
  simp [weilDivisorFiniteDegree, Finsupp.sum_add_index']

/-- The support of a finite-support divisor is finite. -/
theorem weilDivisorFinite_support_finite (E : WeilDivisorFinite X) :
    (E.support : Set (AGCodimOnePoint X)).Finite :=
  E.support.finite_toSet

/-- Sections of a finite-support divisor agree with the sections of its
underlying function-space divisor (definitional). -/
theorem divisorSections_toWeilDivisor_eq (hDVR : CodimOneDVR X) (U : X.Opens) [Nonempty U]
    (E : WeilDivisorFinite X) :
    divisorSections (X := X) hDVR U (toWeilDivisor E) =
      divisorSections (X := X) hDVR U (fun z => E z) :=
  rfl

end LeanFormal.IUT.XiFPaper.AG04FiniteDivisorActual

end
