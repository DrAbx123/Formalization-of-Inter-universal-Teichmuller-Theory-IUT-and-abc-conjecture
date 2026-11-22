import tmp.sheaf.n8.closure.FiniteObservationHullProofs

noncomputable section
namespace LeanFormal.IUT.N8Closure.FiniteObservationHullProofs2
open LeanFormal.IUT.N8Closure.FiniteObservationHull
universe u
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem theoremB_precision_actual
    (G K_N : Subgroup (V ≃ₗ[R] V)) [K_N.Normal]
    (L N : Submodule R V)
    (hKG : K_N ≤ G)
    (hfix : ∀ k : K_N, Submodule.map (k : V →ₗ[R] V) L = L)
    (hker : ∀ g h : G, SameMod N (g : V ≃ₗ[R] V) (h : V ≃ₗ[R] V) →
      (((g⁻¹ * h : G) : V ≃ₗ[R] V)) ∈ K_N) :
    ∀ g h : G, SameMod N (g : V ≃ₗ[R] V) (h : V ≃ₗ[R] V) →
      Submodule.map (g : V →ₗ[R] V) L = Submodule.map (h : V →ₗ[R] V) L := by
  intro g h hsame
  have hk : ((g⁻¹ * h : G) : V ≃ₗ[R] V) ∈ K_N := hker g h hsame
  let k : K_N := ⟨((g⁻¹ * h : G) : V ≃ₗ[R] V), hk⟩
  let kG : G := ⟨k, hKG k.property⟩
  have hmul_G : h = g * kG := by
    change h = g * (g⁻¹ * h)
    group
  have hmul : (h : V ≃ₗ[R] V) = (g : V ≃ₗ[R] V) * (k : V ≃ₗ[R] V) := by
    rw [hmul_G]
    rfl
  have hfixk : Submodule.map (k : V →ₗ[R] V) L = L := hfix k
  calc
    Submodule.map (g : V →ₗ[R] V) L =
        Submodule.map (g : V →ₗ[R] V) (Submodule.map (k : V →ₗ[R] V) L) := by
      rw [hfixk]
    _ = Submodule.map ((g : V →ₗ[R] V).comp (k : V →ₗ[R] V)) L := by
      rw [Submodule.map_comp]
    _ = Submodule.map (h : V →ₗ[R] V) L := by
      rw [hmul, LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp]

end LeanFormal.IUT.N8Closure.FiniteObservationHullProofs2