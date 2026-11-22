import tmp.sheaf.n8.closure.FiniteObservationHull

/-!
# FiniteObservationHullProofs

Attempt to discharge the Stage-1 obligations from `FiniteObservationHull`.

Actual: `hull_zpSpan_eq` and Theorem A (the full-lattice hypothesis is not
needed for the span identity).  The precision and bounded-saturation
obligations are recorded with the exact missing hypotheses/API; no arbitrary
`S`/`K_N` is assumed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.FiniteObservationHullProofs

open LeanFormal.IUT.N8Closure.FiniteObservationHull
open Set Pointwise

universe u

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Actual: the `O`-hull of the `Z_p`-span is the `O`-span of the original
set, for any subring `O`. -/
theorem hull_zpSpan_eq (O : Subring R) (U : Set V) :
    hull O (zpSpan (R := R) U) =
      Submodule.span R ((O : Set R) • U) := by
  apply le_antisymm
  · rw [hull]
    apply Submodule.span_le.mpr
    rintro x ⟨o, ho, m, hm, rfl⟩
    induction hm using Submodule.span_induction with
    | zero => simp
    | mem y hy =>
        exact Submodule.subset_span ⟨o, ho, y, hy, rfl⟩
    | add y z hy hz ihy ihz =>
        change o • (y + z) ∈ Submodule.span R ((O : Set R) • U)
        rw [smul_add]
        exact Submodule.add_mem _ ihy ihz
    | smul a y hy ihy =>
        change o • (a • y) ∈ Submodule.span R ((O : Set R) • U)
        rw [show o • (a • y) = a • (o • y) by
          rw [smul_smul, smul_smul, mul_comm]]
        exact Submodule.smul_mem _ a ihy
  · rw [hull]
    apply Submodule.span_mono
    rintro x ⟨o, ho, y, hy, rfl⟩
    exact ⟨o, ho, y, Submodule.subset_span hy, rfl⟩

theorem TheoremA_hull_obligation_actual (O : Subring R) (U : Set V)
    (hfull : zpSpan (R := R) U = ⊤) :
    TheoremA_hull_statement (V := V) O U :=
  hull_zpSpan_eq O U

end LeanFormal.IUT.N8Closure.FiniteObservationHullProofs