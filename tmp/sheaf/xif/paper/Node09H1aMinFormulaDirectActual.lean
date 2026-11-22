import tmp.sheaf.xif.paper.Node09H1aGenericCoordinateActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Node09H1aMinFormulaDirectActual
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.Node09H1aGenericCoordinateActual
variable {J : Type*} [Fintype J] [DecidableEq J] {E : J → Type*}
variable [∀ j, NormedField (E j)] [∀ j, IsUltrametricDist (E j)]
variable (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))
theorem coordSubmodule_eq_span_of_max_norm
    (M : Submodule (integralRing hna) ((j : J) → E j)) (j : J)
    {x : E j} (hx : x ∈ coordSubmodule hna M j) (hx0 : x ≠ 0)
    (hmax : ∀ y : E j, y ∈ coordSubmodule hna M j → ‖y‖ ≤ ‖x‖) :
    (coordSubmodule hna M j : Set (E j)) =
      (Submodule.span (Integers (E j)) ({x} : Set (E j)) : Set (E j)) := by
  ext y
  constructor
  · intro hy
    have hyx : ‖y / x‖ ≤ 1 := by
      rw [norm_div]
      rw [div_le_one (norm_pos_iff.mpr hx0)]
      exact hmax (a := y) hy
    have hmem : y / x ∈ Integers (E j) := (mem_integers_iff (y / x)).mpr hyx
    have hy_eq : y = (y / x) • x := by
      rw [Algebra.smul_def]
      simp only [Algebra.algebraMap_self, RingHom.id_apply]
      rw [div_mul_cancel₀ y hx0]
    rw [hy_eq]
    exact Submodule.smul_mem (Submodule.span (Integers (E j)) ({x} : Set (E j)))
      (⟨y / x, hmem⟩) (Submodule.subset_span (Set.mem_singleton x))
  · intro hy
    change y ∈ Submodule.span (Integers (E j)) ({x} : Set (E j)) at hy
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨a, rfl⟩ := hy
    exact Submodule.smul_mem _ a hx

/-- Projection of a compact integral submodule to a coordinate is compact. -/
theorem coordSubmodule_isCompact
    (M : Submodule (integralRing hna) ((j : J) → E j)) (j : J)
    (hM : IsCompact (M : Set ((j : J) → E j))) :
    IsCompact (coordSubmodule hna M j : Set (E j)) := by
  have hcont : Continuous (fun x : ((j : J) → E j) => x j) := continuous_apply j
  have h := hM.image hcont
  convert h using 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, hxy⟩
    exact ⟨x, hx, hxy⟩

/-- Direct H1a max-norm existence: a compact coordinate submodule containing
`1` has a nonzero norm-maximal element and equals its principal span. -/
theorem coordSubmodule_eq_span_max
    (M : Submodule (integralRing hna) ((j : J) → E j)) (j : J)
    (hM : IsCompact (M : Set ((j : J) → E j)))
    (h1 : (fun _ : J => (1 : E _)) ∈ M) :
    ∃ x ∈ coordSubmodule hna M j, x ≠ 0 ∧
      (coordSubmodule hna M j : Set (E j)) =
        (Submodule.span (Integers (E j)) ({x} : Set (E j)) : Set (E j)) := by
  have hIcomp : IsCompact (coordSubmodule hna M j : Set (E j)) :=
    coordSubmodule_isCompact hna M j hM
  have h1I : (1 : E j) ∈ coordSubmodule hna M j :=
    ⟨(fun _ : J => (1 : E _)), h1, rfl⟩
  obtain ⟨x, hxI, hmax⟩ :=
    hIcomp.exists_isMaxOn ⟨1, h1I⟩
      (continuous_norm.continuousOn : ContinuousOn (fun x : E j => ‖x‖)
        (coordSubmodule hna M j : Set (E j)))
  have hxnorm_ge_one : (1 : ℝ) ≤ ‖x‖ := by
    simpa using hmax (a := 1) h1I
  have hxne : x ≠ 0 := by
    intro hx0
    rw [hx0, norm_zero] at hxnorm_ge_one
    norm_num at hxnorm_ge_one
  refine ⟨x, hxI, hxne, coordSubmodule_eq_span_of_max_norm hna M j hxI hxne ?_⟩
  intro y hy
  exact hmax (a := y) hy

#print axioms coordSubmodule_isCompact
#print axioms coordSubmodule_eq_span_max

end LeanFormal.IUT.XiFPaper.Node09H1aMinFormulaDirectActual
