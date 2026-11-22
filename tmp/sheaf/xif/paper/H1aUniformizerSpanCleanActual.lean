import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.H1aUniformizerSpanCleanActual
open scoped Pointwise
/-- A principal fractional lattice over a DVR is a uniformizer power. -/
theorem span_singleton_eq_span_uniformizer_zpow
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {π : R} (hπ : Irreducible π) {x : K} (hx : x ≠ 0) :
    ∃ n : Int, Submodule.span R {x} =
      Submodule.span R {((algebraMap R K π) ^ n)} := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hx
  refine ⟨n, ?_⟩
  rw [hu]
  exact (Submodule.span_singleton_eq_span_singleton).mpr ⟨u, rfl⟩ |>.symm
#check span_singleton_eq_span_uniformizer_zpow
end LeanFormal.IUT.XiFPaper.H1aUniformizerSpanCleanActual
end