import LeanFormal.IUT.Foundations.AlgebraicGeometry.SplitCaseGlobalAtoms
import Mathlib.RingTheory.Idempotents
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Atom corners for the M2-global Boolean decomposition

`SplitCaseGlobalAtoms` gives the complete orthogonal Boolean atom family
`e_A = ∏_{p∈A} a p * ∏_{p∉A} (1-a p)`.  This support file proves that on the
corner `S ⧸ (1-e_A)` every coefficient `a p` becomes `0` or `1`, and that the
atoms give the ring product decomposition `S ≃ ∏_A S ⧸ (1-e_A)`.  Consumer:
qside's atomwise M2-global/M3 assembly.
-/
namespace SplitCaseAtomCorners

universe u

variable {S : Type u} [CommRing S] {K : Type u} [Fintype K] [DecidableEq K]

open SplitCaseGlobalAtoms

/-- Multiplication of an atom by a coefficient: `e_A * a p` is `e_A` when
`p ∈ A` and `0` otherwise. -/
lemma epsilonAtom_mul_coeff (a : K → S) (ha : ∀ p, IsIdempotentElem (a p))
    (A : Finset K) (p : K) :
    epsilonAtom a A * a p = if p ∈ A then epsilonAtom a A else 0 := by
  by_cases hp : p ∈ A
  · rw [if_pos hp]
    have hfac : a p ∣ epsilonAtom a A := by
      unfold epsilonAtom
      exact Dvd.dvd.mul_right
        (Finset.dvd_prod_of_mem (s := A) (f := fun x : K => a x) hp) _
    obtain ⟨x, hx⟩ := hfac
    rw [hx]
    calc (a p * x) * a p = (a p * a p) * x := by ring
      _ = a p * x := by rw [(ha p).eq]
  · rw [if_neg hp]
    have hfac : (1 - a p) ∣ epsilonAtom a A := by
      unfold epsilonAtom
      exact Dvd.dvd.mul_left
        (Finset.dvd_prod_of_mem (s := (Finset.univ : Finset K) \ A)
          (f := fun x : K => 1 - a x)
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, hp⟩)) _
    obtain ⟨x, hx⟩ := hfac
    rw [hx]
    calc ((1 - a p) * x) * a p = (1 - a p) * a p * x := by ring
      _ = 0 := by rw [(ha p).one_sub_mul_self, zero_mul]

/-- Multiplication of an atom by `1 - a p`. -/
lemma epsilonAtom_mul_one_sub_coeff (a : K → S) (ha : ∀ p, IsIdempotentElem (a p))
    (A : Finset K) (p : K) :
    epsilonAtom a A * (1 - a p) = if p ∈ A then 0 else epsilonAtom a A := by
  by_cases hp : p ∈ A
  · rw [if_pos hp]
    have hfac : a p ∣ epsilonAtom a A := by
      unfold epsilonAtom
      exact Dvd.dvd.mul_right
        (Finset.dvd_prod_of_mem (s := A) (f := fun x : K => a x) hp) _
    obtain ⟨x, hx⟩ := hfac
    rw [hx]
    calc (a p * x) * (1 - a p) = (a p * (1 - a p)) * x := by ring
      _ = 0 := by rw [(ha p).mul_one_sub_self, zero_mul]
  · rw [if_neg hp]
    have hfac : (1 - a p) ∣ epsilonAtom a A := by
      unfold epsilonAtom
      exact Dvd.dvd.mul_left
        (Finset.dvd_prod_of_mem (s := (Finset.univ : Finset K) \ A)
          (f := fun x : K => 1 - a x)
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, hp⟩)) _
    obtain ⟨x, hx⟩ := hfac
    rw [hx]
    calc ((1 - a p) * x) * (1 - a p) = ((1 - a p) * (1 - a p)) * x := by ring
      _ = (1 - a p) * x := by rw [(ha p).one_sub.eq]

/-- Atom product decomposition of the coefficient ring. -/
noncomputable def atomRingEquiv (a : K → S) (ha : ∀ p, IsIdempotentElem (a p)) :
    S ≃+* ∀ A : Finset K, S ⧸ Ideal.span ({1 - epsilonAtom a A} : Set S) :=
  RingEquiv.ofBijective
    (RingHom.pi fun A => Ideal.Quotient.mk (Ideal.span ({1 - epsilonAtom a A} : Set S)))
    (epsilonAtom_completeOrthogonal a ha).bijective_pi

/-- On each atom corner, every coefficient is `0` or `1`. -/
theorem coeff_eq_zero_or_one_on_corner
    (a : K → S) (ha : ∀ p, IsIdempotentElem (a p)) (A : Finset K) (p : K) :
    Ideal.Quotient.mk (Ideal.span ({1 - epsilonAtom a A} : Set S)) (a p) = 0 ∨
      Ideal.Quotient.mk (Ideal.span ({1 - epsilonAtom a A} : Set S)) (a p) = 1 := by
  let I : Ideal S := Ideal.span ({1 - epsilonAtom a A} : Set S)
  have he : Ideal.Quotient.mk I (epsilonAtom a A) = 1 := by
    rw [← sub_eq_zero]
    change Ideal.Quotient.mk I (epsilonAtom a A) - Ideal.Quotient.mk I (1 : S) = 0
    rw [← map_sub]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [show epsilonAtom a A - 1 = -(1 - epsilonAtom a A) by ring]
    exact I.neg_mem (Ideal.subset_span (by simp [I]))
  have h := congrArg (Ideal.Quotient.mk I) (epsilonAtom_mul_coeff a ha A p)
  simp only [map_mul, he, one_mul] at h
  by_cases hp : p ∈ A
  · right
    rw [if_pos hp] at h
    change Ideal.Quotient.mk I (a p) = 1
    simpa [I, he] using h
  · left
    rw [if_neg hp] at h
    change Ideal.Quotient.mk I (a p) = 0
    simpa [I] using h

end SplitCaseAtomCorners