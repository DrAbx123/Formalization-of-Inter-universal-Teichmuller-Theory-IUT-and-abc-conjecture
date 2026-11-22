import tmp.sheaf.n8.closure.C9HAFullConditional
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Trace-orthogonal complement and the `U = W^perp <-> 1 in U` criterion

Task-226 abstract Lean formalization.  For a finite-dimensional `Q_p`-vector
space `K`, a nonzero trace functional `Tr`, `W = ker Tr`, and a nondegenerate
reflexive bilinear trace pairing `beta` with `beta w one = 0` for `w in W`, we
prove

  `W^perp = span {one}`
  `U = W^perp <-> one in U`  (for a line `U`, `finrank U = 1`).

The last section re-exports the conditional `1 in U => H_A-full and B=O`
statement from `C9HAFullConditional`.

No axiom or sorry; no target/Project edits.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.N8Closure.C9UOrthogonal

universe u

open LeanFormal.IUT.N8Closure.C9HAFullConditional

section TraceSetup

/-- Finite-dimensional Q_p space with trace functional, nondegenerate
reflexive trace pairing, and a chosen line `U`. -/
structure TraceSetup (p : ℕ) [Fact p.Prime] where
  K : Type u
  [addCommGroup : AddCommGroup K]
  [module : Module ℚ_[p] K]
  [finiteDimensional : FiniteDimensional ℚ_[p] K]
  one : K
  Tr : K →ₗ[ℚ_[p]] ℚ_[p]
  hTr : Tr one ≠ 0
  beta : LinearMap.BilinForm ℚ_[p] K
  hbeta : beta.Nondegenerate
  hrefl : beta.IsRefl
  hbeta_one : ∀ w : K, w ∈ LinearMap.ker Tr → beta w one = 0
  U : Submodule ℚ_[p] K
  hUline : Module.finrank ℚ_[p] U = 1

attribute [instance] TraceSetup.addCommGroup TraceSetup.module
attribute [instance] TraceSetup.finiteDimensional

variable {p : ℕ} [Fact p.Prime] (T : TraceSetup.{u} p)

/-- The trace kernel `W = ker Tr`. -/
noncomputable def W : Submodule ℚ_[p] T.K :=
  LinearMap.ker T.Tr

/-- The orthogonal complement `W^perp` with respect to the trace pairing. -/
noncomputable def Wperp : Submodule ℚ_[p] T.K :=
  T.beta.orthogonal (W T)

theorem one_ne_zero : T.one ≠ 0 := by
  intro h
  exact T.hTr (by simp [h])

theorem one_mem_Wperp : T.one ∈ Wperp T := by
  rw [Wperp, LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  exact T.hbeta_one w hw

theorem finrank_W_eq : Module.finrank ℚ_[p] (W T) + 1 = Module.finrank ℚ_[p] T.K := by
  have hTrne : T.Tr ≠ 0 := by
    intro hzero
    exact T.hTr (by simp [hzero])
  unfold W
  exact Module.Dual.finrank_ker_add_one_of_ne_zero (f := T.Tr) hTrne

theorem finrank_Wperp_eq_one : Module.finrank ℚ_[p] (Wperp T) = 1 := by
  have horth := T.beta.finrank_orthogonal T.hbeta (W T)
  have horth' : Module.finrank ℚ_[p] (Wperp T) =
      Module.finrank ℚ_[p] T.K - Module.finrank ℚ_[p] (W T) := by
    unfold Wperp
    exact horth
  have hW := finrank_W_eq T
  rw [horth']
  omega

theorem Wperp_eq_span_one : Wperp T = Submodule.span ℚ_[p] ({T.one} : Set T.K) := by
  have hle : Submodule.span ℚ_[p] ({T.one} : Set T.K) ≤ Wperp T :=
    Submodule.span_le.mpr (by
      rintro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact one_mem_Wperp T)
  have hspan : Module.finrank ℚ_[p] (Submodule.span ℚ_[p] ({T.one} : Set T.K)) = 1 :=
    finrank_span_singleton (one_ne_zero T)
  exact (Submodule.eq_of_le_of_finrank_eq hle
    (by rw [hspan, finrank_Wperp_eq_one T])).symm

theorem U_eq_Wperp_iff_one_mem_U : T.U = Wperp T ↔ T.one ∈ T.U := by
  constructor
  · intro h
    rw [h]
    exact one_mem_Wperp T
  · intro h1
    have hspan_le : Submodule.span ℚ_[p] ({T.one} : Set T.K) ≤ T.U :=
      Submodule.span_le.mpr (by
        rintro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact h1)
    have hUeq : T.U = Submodule.span ℚ_[p] ({T.one} : Set T.K) :=
      (Submodule.eq_of_le_of_finrank_eq hspan_le (by
        rw [finrank_span_singleton (one_ne_zero T), T.hUline])).symm
    rw [hUeq, ← Wperp_eq_span_one T]

end TraceSetup

section Combine

variable {p : ℕ} [Fact p.Prime]
variable (D : DecompData.{u} p)

/-- Combined conditional statement: in a decomposition with `1 in U`, the
`a`-span is `O` (the `H_A-full => B=O` conclusion of
`C9HAFullConditional`). -/
theorem combined_one_mem_U_implies_B_eq (h1 : D.one ∈ D.U)
    (hO : D.O = AddSubgroup.closure (({D.one} : Set D.K) ∪ (D.J : Set D.K))) :
    B_from_a D = D.O :=
  B_from_a_eq_O_of_one_mem_U D h1 hO


/-- Combined form: `1 in U` gives both the `a`-integrality (H_A-full) and
`B = O`. -/
theorem combined_one_mem_U_implies_HA_full_and_B_eq
    (h1 : D.one ∈ D.U) (honeO : D.one ∈ D.O)
    (hO : D.O = AddSubgroup.closure (({D.one} : Set D.K) ∪ (D.J : Set D.K))) :
    (∀ A : D.W →ₗ[ℚ_[p]] D.W, a D A ∈ D.O) ∧ B_from_a D = D.O :=
  ⟨HA_full_a_of_one_mem_U D h1 honeO, combined_one_mem_U_implies_B_eq D h1 hO⟩

end Combine

end LeanFormal.IUT.N8Closure.C9UOrthogonal

end