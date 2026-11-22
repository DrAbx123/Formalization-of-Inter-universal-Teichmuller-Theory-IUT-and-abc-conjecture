import Mathlib.RingTheory.Idempotents
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Boolean idempotent atoms from a finite coefficient set

Given a finite coefficient type K and idempotents a : K → S, the products
  e_A = prod_{p in A} a p * prod_{p in univ \ A} (1 - a p)
form a complete orthogonal family of idempotents indexed by Finset K.
-/

open scoped BigOperators

namespace SplitCaseGlobalAtoms

noncomputable section

universe u

variable {S : Type u} [CommRing S] {K : Type u} [Fintype K] [DecidableEq K]

/-- Boolean idempotent atom associated to a subset A of the coefficient set. -/
def epsilonAtom (a : K → S) (A : Finset K) : S :=
  (∏ p ∈ A, a p) * ∏ p ∈ (Finset.univ : Finset K) \ A, (1 - a p)

lemma epsilonAtom_idempotent (a : K → S) (ha : ∀ p, IsIdempotentElem (a p))
    (A : Finset K) : IsIdempotentElem (epsilonAtom a A) := by
  have hleft : IsIdempotentElem (∏ p ∈ A, a p) := by
    rw [IsIdempotentElem, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p hp => (ha p).eq
  have hright : IsIdempotentElem (∏ p ∈ (Finset.univ : Finset K) \ A, (1 - a p)) := by
    rw [IsIdempotentElem, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun p hp => (ha p).one_sub.eq
  rw [epsilonAtom, IsIdempotentElem]
  rw [mul_mul_mul_comm, hleft.eq, hright.eq]

lemma epsilonAtom_orthogonal (a : K → S) (ha : ∀ p, IsIdempotentElem (a p))
    {A B : Finset K} (hAB : A ≠ B) : epsilonAtom a A * epsilonAtom a B = 0 := by
  have hdiff : ∃ p, (p ∈ A ∧ p ∉ B) ∨ (p ∈ B ∧ p ∉ A) := by
    by_contra h
    apply hAB
    ext p
    constructor
    · intro hp
      by_contra hpb
      exact h ⟨p, Or.inl ⟨hp, hpb⟩⟩
    · intro hp
      by_contra hpa
      exact h ⟨p, Or.inr ⟨hp, hpa⟩⟩
  obtain ⟨p, hp | hp⟩ := hdiff
  · have hpa : p ∈ A := hp.1
    have hpb : p ∉ B := hp.2
    have hzero : a p * (1 - a p) = 0 := (ha p).mul_one_sub_self
    have hA : a p ∣ epsilonAtom a A := by
      unfold epsilonAtom
      exact Dvd.dvd.mul_right (Finset.dvd_prod_of_mem (s := A) (f := fun x : K => a x) hpa) _
    have hB : (1 - a p) ∣ epsilonAtom a B := by
      unfold epsilonAtom
      exact (Finset.dvd_prod_of_mem (s := (Finset.univ : Finset K) \ B)
        (f := fun x : K => 1 - a x)
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, hpb⟩)).mul_left _
    rcases hA with ⟨x, hx⟩; rcases hB with ⟨y, hy⟩
    rw [hx, hy]
    calc (a p * x) * ((1 - a p) * y) = (a p * (1 - a p)) * (x * y) := by ring
      _ = 0 := by rw [hzero, zero_mul]
  · have hpb : p ∈ B := hp.1
    have hpa : p ∉ A := hp.2
    have hzero : (1 - a p) * a p = 0 := (ha p).one_sub_mul_self
    have hA : (1 - a p) ∣ epsilonAtom a A := by
      unfold epsilonAtom
      exact (Finset.dvd_prod_of_mem (s := (Finset.univ : Finset K) \ A)
        (f := fun x : K => 1 - a x)
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, hpa⟩)).mul_left _
    have hB : a p ∣ epsilonAtom a B := by
      unfold epsilonAtom
      exact Dvd.dvd.mul_right (Finset.dvd_prod_of_mem (s := B) (f := fun x : K => a x) hpb) _
    rcases hA with ⟨x, hx⟩; rcases hB with ⟨y, hy⟩
    rw [hx, hy]
    calc ((1 - a p) * x) * (a p * y) = ((1 - a p) * a p) * (x * y) := by ring
      _ = 0 := by rw [hzero, zero_mul]

lemma sum_epsilonAtom_eq_one (a : K → S) (ha : ∀ p, IsIdempotentElem (a p)) :
    (∑ A : Finset K, epsilonAtom a A) = 1 := by
  have huniv : (Finset.univ : Finset (Finset K)) = (Finset.univ : Finset K).powerset := by
    ext A
    simp
  have hprod : (∏ p : K, (a p + (1 - a p))) =
      ∑ A ∈ (Finset.univ : Finset K).powerset, epsilonAtom a A := by
    rw [Finset.prod_add]
    rfl
  have hone : (∏ p : K, (a p + (1 - a p))) = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    ring
  rw [hone] at hprod
  rw [huniv]
  exact hprod.symm

/-- The complete orthogonal family of Boolean atoms. -/
theorem epsilonAtom_completeOrthogonal (a : K → S) (ha : ∀ p, IsIdempotentElem (a p)) :
    CompleteOrthogonalIdempotents (epsilonAtom a) := by
  rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
  constructor
  · intro A B hAB
    exact epsilonAtom_orthogonal a ha hAB
  · exact sum_epsilonAtom_eq_one a ha

end

end SplitCaseGlobalAtoms
