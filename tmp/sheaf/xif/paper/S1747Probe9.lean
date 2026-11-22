import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Artinian.Module
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TensorProduct.Maps

open CategoryTheory
open scoped TensorProduct
open Finset

universe u

namespace S1747Probe

lemma idem_eq_zero_or_one {L : Type} [Field L] {x : L} (hx : IsIdempotentElem x) :
    x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp (show x * (1 - x) = 0 by
    rw [mul_sub, mul_one, hx.eq, sub_self]) with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h).symm

theorem exists_factor {K : Type} [Field K] {J : Type} [Finite J]
    (Bj : J → Type) [∀ j, Field (Bj j)] [∀ j, Algebra K (Bj j)]
    {L : Type} [Field L] [Algebra K L] (ψ : (∀ j, Bj j) →ₐ[K] L) :
    ∃ (j : J) (σ : Bj j →ₐ[K] L), ψ = σ.comp (Pi.evalAlgHom K Bj j) := by
  classical
  haveI : Fintype J := Fintype.ofFinite J
  have hidem : ∀ j, IsIdempotentElem (Pi.single (M := Bj) j 1) := by
    intro j
    ext k
    by_cases h : k = j
    · subst h; simp
    · simp [Pi.single_eq_of_ne, h]
  have horth : ∀ j k, j ≠ k → Pi.single (M := Bj) j 1 * Pi.single (M := Bj) k 1 = 0 := by
    intro j k hjk
    ext l
    by_cases hl : l = j
    · subst hl
      simp [Pi.single_eq_of_ne, hjk]
    · simp [Pi.single_eq_of_ne, hl]
  have hsum : (∑ j, Pi.single (M := Bj) j (1 : Bj j)) = 1 := by
    ext k
    simp
  have hfidem : ∀ j, IsIdempotentElem (ψ (Pi.single (M := Bj) j 1)) := fun j => (hidem j).map ψ
  have hfsum : (∑ j, ψ (Pi.single (M := Bj) j 1)) = 1 := by
    rw [← map_sum, hsum, map_one]
  have hex : ∃ j, ψ (Pi.single (M := Bj) j 1) = 1 := by
    by_contra h
    push_neg at h
    have hzero : ∀ j, ψ (Pi.single (M := Bj) j 1) = 0 := by
      intro j
      rcases idem_eq_zero_or_one (hfidem j) with h0 | h1
      · exact h0
      · exact absurd h1 (h j)
    rw [Finset.sum_congr rfl (fun j _ => hzero j), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_zero] at hfsum
    exact zero_ne_one hfsum
  obtain ⟨j0, hj0⟩ := hex
  have huniq : ∀ j, ψ (Pi.single (M := Bj) j 1) = 1 → j = j0 := by
    intro j hj
    by_contra hne
    have h0 : ψ (Pi.single (M := Bj) j 1) * ψ (Pi.single (M := Bj) j0 1) = 0 := by
      rw [← map_mul, horth j j0 hne, map_zero]
    rw [hj, hj0, one_mul] at h0
    exact one_ne_zero h0
  let σFun : Bj j0 → L := fun y => ψ (Pi.single (M := Bj) j0 y)
  have hσ_one : σFun 1 = 1 := hj0
  have hσ_mul : ∀ x y, σFun (x * y) = σFun x * σFun y := by
    intro x y
    simp only [σFun]
    rw [← map_mul, Pi.single_mul]
  have hσ_zero : σFun 0 = 0 := by simp [σFun]
  have hσ_add : ∀ x y, σFun (x + y) = σFun x + σFun y := by
    intro x y
    simp only [σFun]
    rw [← map_add, Pi.single_add]
  have hσ_smul : ∀ (k : K) (x : Bj j0), σFun (k • x) = k • σFun x := by
    intro k x
    simp only [σFun]
    rw [Pi.single_smul, map_smul]
  let σ : Bj j0 →ₐ[K] L :=
    { toFun := σFun
      map_one' := hσ_one
      map_mul' := hσ_mul
      map_zero' := hσ_zero
      map_add' := hσ_add
      commutes' := fun k => by
        rw [Algebra.algebraMap_eq_smul_one, hσ_smul, hσ_one,
          Algebra.algebraMap_eq_smul_one] }
  refine ⟨j0, σ, ?_⟩
  ext x
  show ψ x = ψ (Pi.single (M := Bj) j0 (x j0))
  conv_lhs => rw [← Finset.univ_sum_single (M := Bj) x]
  rw [map_sum, Finset.sum_eq_single_of_mem j0 (Finset.mem_univ _)]
  intro b _ hb
  have hker : Pi.single (M := Bj) b (x b) =
      Pi.single (M := Bj) b 1 * Pi.single (M := Bj) b (x b) := by
    ext k
    by_cases hk : k = b
    · subst hk; simp
    · simp [Pi.single_eq_of_ne, hk]
  rw [hker, map_mul]
  have hz : ψ (Pi.single (M := Bj) b 1) = 0 := by
    rcases idem_eq_zero_or_one (hfidem b) with h1 | h1
    · exact h1
    · exact absurd (huniq b h1) hb
  rw [hz, zero_mul]

end S1747Probe
