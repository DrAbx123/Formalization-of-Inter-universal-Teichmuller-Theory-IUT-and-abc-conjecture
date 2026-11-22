import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import Mathlib.RingTheory.RootsOfUnity.Basic
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion

/-! # S56: actual O-triangle / O-mu carrier

The paper's O-triangle (O with triangle decoration, extracted as O-triangle) is
the monoid of integral elements of the local field; O-times is its unit group;
O-times-mu is the roots-of-unity subgroup.  These are not the integral ring as a
ring, and not the number-field ring of integers O_k.

This file constructs the actual integral submonoid of the completion and packages
the O-triangle, O-times, and O-times-mu carriers as distinct types.  The source
does not supply a separate boundary type beyond the integral monoid; that is
recorded exactly.

No fake equality/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S56OTriangularCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- Actual O-triangle: the multiplicative monoid of integral elements of the
completion, i.e. the underlying multiplicative monoid of CompletionIntegers. -/
noncomputable def oTriangularMonoid :
    Submonoid (CommonPrimeCompletion place) :=
  (CompletionIntegers place.val).toSubring.toSubmonoid

/-- Actual O-times: the unit group of the integral ring. -/
abbrev oTimesUnits : Type u := (CompletionIntegers place.val)ˣ

/-- Actual O-times-mu: the roots of unity in the integral ring's units. -/
noncomputable def oTimesMu : Subgroup (CompletionIntegers place.val)ˣ :=
  rootsOfUnity (2 * l.value) (CompletionIntegers place.val)

/-- The O-triangle monoid is a multiplicative submonoid, not the integral ring
as an additive ring. -/
structure ODecoratedCarrierAudit where
  triangular : Type u
  triangular_eq : triangular = oTriangularMonoid (K := K) (p := p) place
  units : Type u
  units_eq : units = oTimesUnits (K := K) (p := p) place
  roots : Type u
  roots_eq : roots = oTimesMu (l := l) (K := K) (p := p) place

/-- Actual packaging of the three O carriers. -/
noncomputable def oDecoratedCarrierAudit :
    ODecoratedCarrierAudit (l := l) (K := K) (p := p) place where
  triangular := oTriangularMonoid (K := K) (p := p) place
  triangular_eq := rfl
  units := oTimesUnits (K := K) (p := p) place
  units_eq := rfl
  roots := oTimesMu (l := l) (K := K) (p := p) place
  roots_eq := rfl

/-- Exact missing source field: a separate boundary decoration type for
O-triangle beyond the integral monoid. -/
structure OBoundaryDecorationGap where
  carrier : Type u
  carrier_eq : carrier = oTriangularMonoid (K := K) (p := p) place
  boundaryField : Type u

/-- The exact O-boundary decoration requirement; no inhabitant asserted. -/
def OBoundaryDecorationRequired : Prop :=
  Nonempty (OBoundaryDecorationGap (K := K) (p := p) place)

end LeanFormal.IUT.XiFPaper.S56OTriangularCarrierActual

end
