/- A3 (route §4.2 L296 official shortcut): the B2 evaluation lemma, abstract linear-algebra core.

  Route §4.1 L251-261: for each point x of the divisor D_T the evaluation of global sections
  at x is a nonzero linear map, so its kernel is a proper subspace; finitely many proper
  subspaces cannot cover a vector space over the infinite field ℚ, hence there is a section
  s₁ which is nonzero at every point of D_T. This file proves that linear-algebra step in the
  generality needed (varying residue fields, over any infinite field), using Mathlib's
  `Subspace.exists_eq_top_of_iUnion_eq_univ` (finite union of proper subspaces cannot cover).

  OBLIGATIONS (registered, NOT claimed; see coord/EXPLICIT-PARAM-AUDIT-GRACE.md §E):
  (i) produce the nonzero evaluation maps `H⁰(O(D_T)) → residue field at x` for every closed
      point x of D_T -- route L257: negative-degree line bundle has no nonzero section, so
      H¹(O(D_T - x)) = 0 via Serre duality (donor: AG_FLT_ProvedTheoremsPromotionActual.
      promotion_serrePairing_bijective_and_flip_bijective, which currently takes
      `(hC : ConstantsAreBase K F) (hRT : ResidueTheorem K F)` and the curve instances);
  (ii) Galois-compatible closed-point evaluations (route L259: geometric-point proof plus
      H⁰ field-extension compatibility; no separate ℚ̄→ℚ descent needed);
  (iii) landing s₀/s₁ in the fixed chart rings (PsiGeneralRRData interface, DONE 05:26:49).
  No sorry/axiom. -/
import Mathlib.GroupTheory.CosetCover
import Mathlib.Tactic

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1A3EvaluationActual

/-- **B2 evaluation lemma (linear-algebra core).** Over an infinite field `k`, given finitely
    many linear maps `ev i : V →ₗ[k] K i` to (possibly different) residue fields, each nonzero,
    there is a vector on which all of them are nonzero. -/
theorem exists_forall_apply_ne_zero
    {k : Type*} [Field k] [Infinite k]
    {V : Type*} [AddCommGroup V] [Module k V]
    {ι : Type*} (s : Finset ι) (K : ι → Type*) [∀ i, Field (K i)] [∀ i, Algebra k (K i)]
    (ev : ∀ i, V →ₗ[k] K i) (nev : ∀ i ∈ s, ev i ≠ 0) :
    ∃ v : V, ∀ i ∈ s, ev i v ≠ 0 := by
  classical
  have hne : ∀ i ∈ s, (LinearMap.ker (ev i) : Submodule k V) ≠ ⊤ := by
    intro i hi h
    apply nev i hi
    refine LinearMap.ext (fun v => ?_)
    have hv : v ∈ LinearMap.ker (ev i) := by rw [h]; exact Submodule.mem_top
    simpa [LinearMap.mem_ker] using hv
  by_contra h
  push_neg at h
  let p : ↥s → Submodule k V := fun i => LinearMap.ker (ev i.1)
  have hcov : ⋃ i, (p i : Set V) = Set.univ := by
    ext v
    constructor
    · intro _; exact Set.mem_univ v
    · intro _
      obtain ⟨i, hi, hai⟩ := h v
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, by simpa [p, LinearMap.mem_ker] using hai⟩
  obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ (p := p) hcov
  exact hne i.1 i.2 (by simpa [p] using hi)

#print axioms exists_forall_apply_ne_zero

end LeanFormal.IUT.XiFPaper.Mzk1G1A3EvaluationActual
