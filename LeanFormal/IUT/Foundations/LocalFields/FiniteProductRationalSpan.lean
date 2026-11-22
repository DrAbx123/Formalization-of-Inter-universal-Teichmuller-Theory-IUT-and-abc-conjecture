import Mathlib.LinearAlgebra.Pi

/-! Rational generation of a finite product by coordinatewise integral regions. -/

namespace LeanFormal.IUT.FiniteProductRationalSpan

variable {ι : Type*} [Finite ι] {M : ι → Type*}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module ℚ (M i)]

theorem rat_span_pi_eq_top (S : (i : ι) → Set (M i))
    (hzero : ∀ i, 0 ∈ S i) (hspan : ∀ i, Submodule.span ℚ (S i) = ⊤) :
    Submodule.span ℚ (Set.pi Set.univ S) = ⊤ := by
  classical
  letI := Fintype.ofFinite ι
  let P := Submodule.span ℚ (Set.pi Set.univ S)
  have hsingle : ∀ i (x : M i), Pi.single i x ∈ P := by
    intro i x
    have hx : x ∈ Submodule.span ℚ (S i) := by rw [hspan]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
        apply Submodule.subset_span
        intro j _
        by_cases hji : j = i
        · subst j
          simpa using hx
        · simp only [Pi.single_eq_of_ne hji]
          exact hzero j
    | zero => simp
    | add x y _ _ hx hy => simpa only [Pi.single_add] using P.add_mem hx hy
    | smul r x _ hx => simpa only [Pi.single_smul] using P.smul_mem r hx
  apply Submodule.eq_top_iff'.mpr
  intro x
  have hsum : ∑ i, Pi.single i (x i) = x := Finset.univ_sum_single x
  rw [← hsum]
  exact P.sum_mem (fun i _ => hsingle i (x i))

end LeanFormal.IUT.FiniteProductRationalSpan
