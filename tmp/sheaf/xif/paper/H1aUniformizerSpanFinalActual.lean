/- H1a DVR factor: a nonzero element of a discrete valuation ring is a unit
times a power of a uniformizer, so its principal span is the span of that
uniformizer power.  Uses the existing Mathlib DVR factorization. -/
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.H1aUniformizerSpanFinalActual

/-- Unit-times-uniformizer-power form of the DVR factorization. -/
theorem exists_unit_mul_uniformizer_pow
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {pi x : R} (hpi : Irreducible pi) (hx : x ≠ 0) :
    ∃ (r : Nat) (u : Rˣ), x = (u : R) * pi ^ r :=
  IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hpi

/-- Span form of the DVR factorization: the principal span of a nonzero
element is the span of a power of the uniformizer. -/
theorem exists_span_singleton_eq_span_uniformizer_pow
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {pi x : R} (hpi : Irreducible pi) (hx : x ≠ 0) :
    ∃ r : Nat, Submodule.span R {x} = Submodule.span R {pi ^ r} := by
  obtain ⟨r, u, hu⟩ := exists_unit_mul_uniformizer_pow (R := R) hpi hx
  refine ⟨r, ?_⟩
  rw [hu]
  exact Ideal.span_singleton_mul_left_unit (a := (u : R)) u.isUnit (pi ^ r)

#print axioms exists_unit_mul_uniformizer_pow
#print axioms exists_span_singleton_eq_span_uniformizer_pow

end LeanFormal.IUT.XiFPaper.H1aUniformizerSpanFinalActual
end
