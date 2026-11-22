import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

namespace ABCBridge.BooleanIdempotentAtoms

noncomputable section

universe u

variable {S : Type u} [CommRing S] [DecidableEq S]

noncomputable def atomOf (T : Finset S) (A : Finset S) : S :=
  ∏ t ∈ T, if t ∈ A then t else 1 - t

abbrev AtomIndex (T : Finset S) : Type u := ↥T.powerset

instance atomIndexFintype (T : Finset S) : Fintype (AtomIndex T) := inferInstance

noncomputable def atom (T : Finset S) (A : AtomIndex T) : S := atomOf T A.1

theorem atomOf_eq_prod (T A : Finset S) (hA : A ⊆ T) :
    atomOf T A = (∏ t ∈ A, t) * ∏ t ∈ T \ A, (1 - t) := by
  unfold atomOf
  rw [Finset.prod_ite]
  rw [Finset.filter_mem_eq_inter, Finset.inter_comm, Finset.inter_eq_left.mpr hA]
  rw [Finset.filter_notMem_eq_sdiff]

theorem isIdempotentElem_prod {ι : Type*} (s : Finset ι) (f : ι → S)
    (h : ∀ i ∈ s, IsIdempotentElem (f i)) :
    IsIdempotentElem (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [IsIdempotentElem]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (h a (by simp)).mul (ih (fun i hi => h i (by simp [hi])))

theorem atomOf_idempotent (T : Finset S) (hT : ∀ t ∈ T, IsIdempotentElem t)
    (A : Finset S) : IsIdempotentElem (atomOf T A) := by
  unfold atomOf
  apply isIdempotentElem_prod
  intro t ht
  by_cases hmem : t ∈ A
  · simpa [hmem] using hT t ht
  · simpa [hmem] using (hT t ht).one_sub

theorem atoms_completeOrthogonal (T : Finset S)
    (hT : ∀ t ∈ T, IsIdempotentElem t) :
    CompleteOrthogonalIdempotents (fun A : AtomIndex T => atom T A) where
  idem A := atomOf_idempotent T hT A.1
  ortho := by
    intro A B hAB
    have hAsub : (A : Finset S) ⊆ T := Finset.mem_powerset.mp A.2
    have hBsub : (B : Finset S) ⊆ T := Finset.mem_powerset.mp B.2
    have hne : ∃ t, (t ∈ (A : Finset S) ∧ t ∉ (B : Finset S)) ∨
        (t ∈ (B : Finset S) ∧ t ∉ (A : Finset S)) := by
      by_contra h
      push_neg at h
      apply hAB
      ext t
      exact ⟨(h t).1, (h t).2⟩
    obtain ⟨t, ht⟩ := hne
    have htT : t ∈ T := ht.elim (fun h => hAsub h.1) (fun h => hBsub h.1)
    have hzero : (if t ∈ (A : Finset S) then t else 1 - t) *
        (if t ∈ (B : Finset S) then t else 1 - t) = 0 := by
      rcases ht with ⟨hA, hB⟩ | ⟨hB, hA⟩
      · simp [hA, hB, (hT t htT).mul_one_sub_self]
      · simp [hA, hB, (hT t htT).one_sub_mul_self]
    unfold atom atomOf
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_zero htT hzero
  complete := by
    classical
    rw [show (∑ A : AtomIndex T, atom T A) =
        ∑ A ∈ T.powerset, atomOf T A by
      rw [← Finset.sum_attach T.powerset (fun A => atomOf T A)]
      simp [atom, Finset.univ_eq_attach]]
    rw [show (∑ A ∈ T.powerset, atomOf T A) =
        ∑ A ∈ T.powerset, (∏ t ∈ A, t) * ∏ t ∈ T \ A, (1 - t) by
      apply Finset.sum_congr rfl
      intro A hA
      exact atomOf_eq_prod T A (Finset.mem_powerset.mp hA)]
    rw [← Finset.prod_add (fun t : S => t) (fun t : S => 1 - t) T]
    apply Finset.prod_eq_one
    intro t ht
    ring

/-- The Boolean atom decomposition `S ≃ ∏_ε S ⧸ (1 - e_ε)`. -/
noncomputable def atomsRingEquiv (T : Finset S)
    (hT : ∀ t ∈ T, IsIdempotentElem t) :
    S ≃+* Π A : AtomIndex T, S ⧸ Ideal.span ({1 - atom T A} : Set S) :=
  RingEquiv.ofBijective
    (RingHom.pi fun A => Ideal.Quotient.mk (Ideal.span {1 - atom T A}))
    (atoms_completeOrthogonal T hT).bijective_pi

end

end ABCBridge.BooleanIdempotentAtoms
