import LeanFormal.IUT.Foundations.AlgebraicGeometry.PermutationTorsorQuotient
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace ABCBridge.M2GlobalSupport

noncomputable section

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] {ι : Type u} [Fintype ι]

/-- Package: fixed points of a finite coordinate-permutation action are functions on
the orbit quotient.  The `MulAction` on the index is the one induced by `ρ`. -/
theorem fixedPoints_permutation (ρ : G →* Equiv.Perm ι) :
    letI : MulAction G ι := MulAction.compHom ι ρ
    Nonempty (FixedPoints.subalgebra R (ι → R) G ≃ₐ[R]
      (MulAction.orbitRel.Quotient G ι → R)) := by
  letI : MulAction G ι := MulAction.compHom ι ρ
  exact ⟨PermutationTorsorQuotient.fixedPointsEquivOrbitFunctions
    (R := R) (G := G) (ι := ι)⟩

theorem fixedPoints_permutation_finiteEtale (ρ : G →* Equiv.Perm ι) :
    letI : MulAction G ι := MulAction.compHom ι ρ
    Algebra.Etale R (FixedPoints.subalgebra R (ι → R) G) ∧
      Module.Finite R (FixedPoints.subalgebra R (ι → R) G) := by
  letI : MulAction G ι := MulAction.compHom ι ρ
  exact PermutationTorsorQuotient.fixedPoints_finiteEtale_orbits
    (R := R) (G := G) (ι := ι)

section PermOfCoeffZeroOne

variable {S : Type u} [CommRing S] [Nontrivial S]

theorem stdIdem_sum {n : ℕ} :
    (∑ i : Fin n, (Pi.single i (1 : S) : Fin n → S)) = 1 := by
  funext j
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne (Ne.symm hij)]
  · intro hj
    simp at hj

theorem stdIdem_mul_of_ne {n : ℕ} {i k : Fin n} (hik : i ≠ k) :
    (Pi.single i (1 : S) : Fin n → S) * Pi.single k (1 : S) = 0 := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [Pi.single_eq_same, Pi.single_eq_of_ne hik]
  · simp [Pi.single_eq_of_ne hj]

theorem stdIdem_idem {n : ℕ} (i : Fin n) :
    IsIdempotentElem (Pi.single i (1 : S) : Fin n → S) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

theorem stdIdem_ne_zero {n : ℕ} (i : Fin n) :
    (Pi.single i (1 : S) : Fin n → S) ≠ 0 := by
  intro h
  have := congrFun h i
  simpa using this

theorem perm_of_coeff_zero_one {n : ℕ}
    (σ : (Fin n → S) ≃ₐ[S] (Fin n → S))
    (h01 : ∀ i j, σ (Pi.single i (1 : S)) j = 0 ∨ σ (Pi.single i (1 : S)) j = 1) :
    ∃ π : Equiv.Perm (Fin n), ∀ i, σ (Pi.single i (1 : S)) = Pi.single (π i) 1 := by
  classical
  let M : Fin n → Fin n → S := fun i j => σ (Pi.single i (1 : S)) j
  have hcol : ∀ j, (∑ i, M i j) = 1 := by
    intro j
    have hsum : σ (∑ i : Fin n, (Pi.single i (1 : S) : Fin n → S)) = 1 := by
      rw [stdIdem_sum, map_one]
    have hmap := congrFun (map_sum σ (fun i : Fin n => (Pi.single i (1 : S) : Fin n → S)) Finset.univ) j
    rw [hsum] at hmap
    simpa [M] using hmap.symm
  have horth : ∀ i k j, i ≠ k → M i j * M k j = 0 := by
    intro i k j hik
    have hzero : σ (Pi.single i (1 : S) : Fin n → S) * σ (Pi.single k (1 : S) : Fin n → S) = 0 := by
      rw [← map_mul, stdIdem_mul_of_ne hik, map_zero]
    exact congrFun hzero j
  have hcol_unique : ∀ j, ∃! i, M i j = 1 := by
    intro j
    have hex : ∃ i, M i j = 1 := by
      by_contra h
      push_neg at h
      have hzero : (∑ i, M i j) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rcases h01 i j with h0 | h1
        · exact h0
        · exact absurd h1 (h i)
      rw [hcol j] at hzero
      exact one_ne_zero hzero
    obtain ⟨i, hi⟩ := hex
    refine ⟨i, hi, ?_⟩
    intro k hk
    by_contra hki
    have hzero := horth k i j hki
    rw [hk, hi, one_mul] at hzero
    exact one_ne_zero hzero
  let τ : Fin n → Fin n := fun j => (hcol_unique j).exists.choose
  have hτ : ∀ j, M (τ j) j = 1 := fun j => (hcol_unique j).exists.choose_spec
  have hτ_unique : ∀ j i, M i j = 1 → i = τ j :=
    fun j i hi => (hcol_unique j).unique hi (hτ j)
  have hrow_nonempty : ∀ i, ∃ j, M i j = 1 := by
    intro i
    by_contra h
    push_neg at h
    have hzero : σ (Pi.single i (1 : S) : Fin n → S) = 0 := by
      funext j
      rcases h01 i j with h0 | h1
      · exact h0
      · exact absurd h1 (h j)
    exact stdIdem_ne_zero i (σ.injective (by simpa [M] using hzero))
  have hτ_surj : Function.Surjective τ := by
    intro i
    obtain ⟨j, hj⟩ := hrow_nonempty i
    exact ⟨j, (hτ_unique j i hj).symm⟩
  have hτ_inj : Function.Injective τ :=
    Finite.injective_iff_surjective.mpr hτ_surj
  let τEquiv : Equiv.Perm (Fin n) := Equiv.ofBijective τ ⟨hτ_inj, hτ_surj⟩
  let π : Equiv.Perm (Fin n) := τEquiv.symm
  have hπ : ∀ i, τ (π i) = i := fun i => τEquiv.apply_symm_apply i
  refine ⟨π, fun i => ?_⟩
  funext j
  by_cases hj : j = π i
  · have hτi : τ (π i) = i := hπ i
    have h1 : M i (π i) = 1 := by
      simpa [hτi] using hτ (π i)
    subst hj
    simpa [M] using h1
  · have hne : M i j ≠ 1 := by
      intro h1
      have hji : j = π i := by
        have hi : τ j = i := (hτ_unique j i h1).symm
        have hτπ : τ j = τ (π i) := by rw [hi, hπ i]
        exact hτ_inj hτπ
      exact hj hji
    rcases h01 i j with h0 | h1
    · simp [hj, h0]
    · exact absurd h1 hne

end PermOfCoeffZeroOne

end

end ABCBridge.M2GlobalSupport
