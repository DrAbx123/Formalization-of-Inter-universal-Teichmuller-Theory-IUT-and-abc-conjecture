import tmp.sheaf.n8.closure.FiniteObservationHullProofs2
import Mathlib.Data.Set.Card

set_option maxHeartbeats 800000

noncomputable section
namespace LeanFormal.IUT.N8Closure.FiniteObservationHullProofs3
open LeanFormal.IUT.N8Closure.FiniteObservationHull
universe u
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable {ι : Type u} [Fintype ι] [Fintype V]

theorem satStep_mono (g : ι → (V ≃ₗ[R] V)) {M N : Submodule R V} (h : M ≤ N) :
    satStep g M ≤ satStep g N := by
  apply sup_le
  · exact h.trans le_sup_left
  · refine iSup_le fun i => ?_
    unfold satStep
    exact ((Submodule.map_mono (f := (g i : V →ₗ[R] V)) h).trans
      (le_iSup (fun i => Submodule.map (g i : V →ₗ[R] V) N) i)).trans le_sup_right

theorem satIter_mono (g : ι → (V ≃ₗ[R] V)) (n : ℕ) {M N : Submodule R V}
    (h : M ≤ N) : satIter g n M ≤ satIter g n N := by
  induction n generalizing M N with
  | zero => exact h
  | succ n ih => exact ih (satStep_mono g h)

theorem satIter_succ (g : ι → (V ≃ₗ[R] V)) (n : ℕ) (M : Submodule R V) :
    satIter g (n + 1) M = satStep g (satIter g n M) := by
  induction n generalizing M with
  | zero => rfl
  | succ n ih => exact ih (satStep g M)

def M (g : ι → (V ≃ₗ[R] V)) (M0 : Submodule R V) (n : ℕ) : Submodule R V :=
  satIter g n M0

theorem chain_le (g : ι → (V ≃ₗ[R] V)) (M0 : Submodule R V) (n : ℕ) :
    M g M0 n ≤ M g M0 (n + 1) := by
  change satIter g n M0 ≤ satIter g n (satStep g M0)
  exact satIter_mono g n le_sup_left

def f (g : ι → (V ≃ₗ[R] V)) (M0 : Submodule R V) (n : ℕ) : ℕ :=
  (M g M0 n : Set V).ncard

theorem f_step (g : ι → (V ≃ₗ[R] V)) (M0 : Submodule R V) (n : ℕ) :
    f g M0 n ≤ f g M0 (n + 1) := by
  exact Set.ncard_le_ncard (chain_le g M0 n)

theorem f_mono (g : ι → (V ≃ₗ[R] V)) (M0 : Submodule R V) :
    Monotone (f g M0) := monotone_nat_of_le_succ (f_step g M0)

theorem f_bound (g : ι → (V ≃ₗ[R] V)) (M0 : Submodule R V) (n : ℕ) :
    f g M0 n ≤ Nat.card V := by
  rw [← Set.ncard_univ (α := V)]
  exact Set.ncard_le_ncard (Set.subset_univ _)

theorem eq_of_le_of_ncard_eq {M N : Submodule R V} (hMN : M ≤ N)
    (hcard : (N : Set V).ncard ≤ (M : Set V).ncard) : M = N := by
  have hset : (M : Set V) = (N : Set V) := Set.eq_of_subset_of_ncard_le hMN hcard
  apply le_antisymm hMN
  intro x
  have hx : x ∈ (M : Set V) ↔ x ∈ (N : Set V) := by rw [hset]
  exact hx.mpr

theorem f_stab (g : ι → (V ≃ₗ[R] V)) (M0 : Submodule R V) (m : ℕ)
    (h : f g M0 m = f g M0 (m + 1)) :
    f g M0 (m + 1) = f g M0 (m + 2) := by
  have hm : M g M0 m = M g M0 (m + 1) :=
    eq_of_le_of_ncard_eq (chain_le g M0 m) (le_of_eq h.symm)
  have hM : M g M0 (m + 2) = M g M0 (m + 1) := by
    calc
      M g M0 (m + 2) = satStep g (M g M0 (m + 1)) := satIter_succ g (m+1) M0
      _ = satStep g (M g M0 m) := by rw [hm]
      _ = M g M0 (m + 1) := (satIter_succ g m M0).symm
  change (M g M0 (m + 1) : Set V).ncard = (M g M0 (m + 2) : Set V).ncard
  rw [hM]

theorem bounded_saturation_actual (g : ι → (V ≃ₗ[R] V)) (M0 : Submodule R V) :
    ∃ k ≤ Nat.card V, satIter g k (satStep g M0) = satIter g k M0 := by
  let b := Nat.card V
  have hstab : f g M0 (b + 1) = f g M0 b :=
    Nat.stabilises_of_monotone (f_mono g M0) (f_bound g M0) (f_stab g M0) (Nat.le_succ b)
  refine ⟨b, le_rfl, ?_⟩
  have hle : M g M0 b ≤ satIter g b (satStep g M0) := by
    change M g M0 b ≤ M g M0 (b + 1)
    exact chain_le g M0 b
  have hcard : (satIter g b (satStep g M0) : Set V).ncard =
      (M g M0 b : Set V).ncard := by
    have hs : satIter g (b + 1) M0 = satIter g b (satStep g M0) := rfl
    rw [← hs]
    simpa [f, M] using hstab
  exact (eq_of_le_of_ncard_eq hle (le_of_eq hcard)).symm

end LeanFormal.IUT.N8Closure.FiniteObservationHullProofs3