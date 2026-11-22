import tmp.sheaf.xif.paper.S56OTriangularCarrierActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion

/-! # S60: O-triangle versus O-boundary

Source reading (Hoshi, local p-adic setup):

* O-triangle = {a | |a| <= 1} = integral monoid, including 0;
* O-boundary (O, triangle-with-boundary) = {a | 0 < |a| <= 1} = nonzero integral
  elements, a monoid under multiplication;
* O-times = units {|a| = 1};
* O-times-mu = roots of unity in the units.

S56 constructed O-triangle as the integral submonoid.  This file constructs the
actual O-boundary submonoid of nonzero integral elements, together with its
inclusion into O-triangle, and packages the distinct carriers.  O-boundary is
not identified with O-triangle or with the integral ring.

No fake equality/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S60OTriangleBoundaryActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S56OTriangularCarrierActual

universe u

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- Actual O-boundary: nonzero integral elements {0 < |a| <= 1}, a
multiplicative submonoid of the completion. -/
noncomputable def oBoundaryMonoid :
    Submonoid (CommonPrimeCompletion place) where
  carrier := {x | x ∈ CompletionIntegers place.val ∧ x ≠ 0}
  one_mem' := by
    refine ⟨?_, one_ne_zero⟩
    exact (CompletionIntegers place.val).one_mem
  mul_mem' := by
    rintro x y ⟨hx, hx0⟩ ⟨hy, hy0⟩
    refine ⟨?_, mul_ne_zero hx0 hy0⟩
    exact (CompletionIntegers place.val).mul_mem x y hx hy

/-- O-boundary injects into O-triangle by forgetting nonvanishing. -/
def oBoundaryToTriangular :
    oBoundaryMonoid (K := K) (p := p) place →
      oTriangularMonoid (K := K) (p := p) place :=
  fun x => ⟨x.1, x.2.1⟩

/-- The O-boundary element is nonzero, unlike an arbitrary O-triangle element. -/
theorem oBoundary_ne_zero (x : oBoundaryMonoid (K := K) (p := p) place) :
    (x : CommonPrimeCompletion place) ≠ 0 := x.2.2

/-- Actual carrier packaging: O-triangle, O-boundary, O-times, O-times-mu are
different types. -/
structure OTriangleBoundaryCarriers where
  triangular : Type u
  triangular_eq : triangular = oTriangularMonoid (K := K) (p := p) place
  boundary : Type u
  boundary_eq : boundary = oBoundaryMonoid (K := K) (p := p) place
  units : Type u
  units_eq : units = oTimesUnits (K := K) (p := p) place
  roots : Type u
  roots_eq : roots = oTimesMu (l := l) (K := K) (p := p) place

/-- Actual packaging of the O carriers. -/
noncomputable def oTriangleBoundaryCarriers :
    OTriangleBoundaryCarriers (l := l) (K := K) (p := p) place where
  triangular := oTriangularMonoid (K := K) (p := p) place
  triangular_eq := rfl
  boundary := oBoundaryMonoid (K := K) (p := p) place
  boundary_eq := rfl
  units := oTimesUnits (K := K) (p := p) place
  units_eq := rfl
  roots := oTimesMu (l := l) (K := K) (p := p) place
  roots_eq := rfl

end LeanFormal.IUT.XiFPaper.S60OTriangleBoundaryActual

end
