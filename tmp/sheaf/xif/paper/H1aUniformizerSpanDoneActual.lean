import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.H1aUniformizerSpanDoneActual
open scoped Pointwise
/-- A principal fractional lattice over a DVR is a power of a uniformizer. -/
theorem span_singleton_eq_span_uniformizer_zpow
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {π : R} (hπ : Irreducible π) {x : K} (hx : x ≠ 0) :
    ∃ n : Int, Submodule.span R {x} =
      Submodule.span R {((algebraMap R K π) ^ n)} := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hx
  refine ⟨n, ?_⟩
  rw [hu]
  apply le_antisymm
  · rw [Submodule.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have h : ((u⁻¹ : Rˣ) : R) • (u • (algebraMap R K) π ^ n) = (algebraMap R K) π ^ n := by
      rw [smul_smul]
      simp
    rw [← h]
    exact Submodule.smul_mem _ ((u⁻¹ : Rˣ) : R) (Submodule.subset_span (Set.mem_singleton _))
  · rw [Submodule.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    simpa [Units.smul_def] using
      (Submodule.smul_mem (Submodule.span R {u • (algebraMap R K) π ^ n}) ((u : Rˣ) : R)
        (Submodule.subset_span (Set.mem_singleton _)))
#check span_singleton_eq_span_uniformizer_zpow
end LeanFormal.IUT.XiFPaper.H1aUniformizerSpanDoneActual
end
-- mark 1794767880336
