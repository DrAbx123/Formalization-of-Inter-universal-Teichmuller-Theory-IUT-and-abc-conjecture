import tmp.sheaf.xif.paper.Mzk1G1ProtectedToZeroMapActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1TwoSectionDataActual
open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1ProtectedToZeroMapActual

variable {K : Type*} [Field K] [DecidableEq K]

/-- Actual two-section data on a commutative ring: two global sections whose
span is the unit ideal, so they have no common zero at any prime.  The
nonvanishing fields are part of the data (both sections are genuine, nonzero). -/
structure TwoSectionData (A : Type*) [CommRing A] where
  s0 : A
  s1 : A
  span_top : Ideal.span ({s0, s1} : Set A) = ⊤
  s0_ne_zero : s0 ≠ 0
  s1_ne_zero : s1 ≠ 0

/-- Unit-ideal two sections have no common zero at any prime. -/
theorem not_both_mem_of_span_top {A : Type*} [CommRing A]
    {s0 s1 : A} (h : Ideal.span ({s0, s1} : Set A) = ⊤)
    (P : Ideal A) [P.IsPrime] : ¬ (s0 ∈ P ∧ s1 ∈ P) := by
  rintro ⟨h0, h1⟩
  have hle : Ideal.span ({s0, s1} : Set A) ≤ P :=
    Ideal.span_le.mpr (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx; rcases hx with rfl | rfl <;> assumption)
  rw [h] at hle
  have htop : P = ⊤ := top_le_iff.mp hle
  exact (Ideal.IsPrime.ne_top (inferInstance : P.IsPrime)) htop

/-- The zero set of the protected-to-zero polynomial is EXACTLY the protected set:
the divisor of s0 is supported precisely on T. -/
theorem eval_protectedToZero_eq_zero_iff {T : Finset K} {a : K} :
    Polynomial.eval a (protectedToZeroPolynomial T) = 0 ↔ a ∈ T := by
  induction T using Finset.induction_on with
  | empty => simp [protectedToZeroPolynomial]
  | insert b s hb ih =>
      unfold protectedToZeroPolynomial
      rw [Finset.prod_insert hb, Polynomial.eval_mul, mul_eq_zero, Finset.mem_insert]
      constructor
      · rintro (h | h)
        · left
          exact sub_eq_zero.mp (by simpa using h)
        · exact Or.inr (ih.mp h)
      · rintro (rfl | h)
        · left
          simp
        · exact Or.inr (ih.mpr h)

/-- The protected-to-zero polynomial is monic. -/
theorem protectedToZeroPolynomial_monic (T : Finset K) :
    (protectedToZeroPolynomial T).Monic := by
  unfold protectedToZeroPolynomial
  exact Polynomial.monic_prod_of_monic T _ (fun t _ => Polynomial.monic_X_sub_C t)

/-- The protected-to-zero section is a genuine nonzero global section. -/
theorem protectedToZeroPolynomial_ne_zero (T : Finset K) :
    protectedToZeroPolynomial T ≠ 0 :=
  (protectedToZeroPolynomial_monic T).ne_zero

/-- Every protected point is a SIMPLE zero: the local vanishing order at t in T
is exactly 1.  This is the divisor-level form of "the whole 0-fiber is
unramified over 0". -/
theorem rootMultiplicity_protectedToZero_of_mem {T : Finset K} {t : K} (ht : t ∈ T) :
    Polynomial.rootMultiplicity t (protectedToZeroPolynomial T) = 1 := by
  have hsplit : protectedToZeroPolynomial T =
      (Polynomial.X - Polynomial.C t) * protectedToZeroPolynomial (T.erase t) := by
    unfold protectedToZeroPolynomial
    rw [← Finset.mul_prod_erase T (fun s => (Polynomial.X - Polynomial.C s)) ht]
  have hq : protectedToZeroPolynomial (T.erase t) ≠ 0 := protectedToZeroPolynomial_ne_zero _
  have hqeval : Polynomial.eval t (protectedToZeroPolynomial (T.erase t)) ≠ 0 := by
    intro h
    have hmem : t ∈ T.erase t := eval_protectedToZero_eq_zero_iff.mp h
    exact (Finset.mem_erase.mp hmem).1 rfl
  rw [hsplit, Polynomial.rootMultiplicity_mul (mul_ne_zero (Polynomial.monic_X_sub_C t).ne_zero hq),
    Polynomial.rootMultiplicity_X_sub_C, Polynomial.rootMultiplicity_eq_zero hqeval]
  simp

/-- The protected polynomial together with the constant 1 give actual
two-section data: the zero divisor of s0 is supported on T, while s1 = 1
never vanishes on T. -/
def protectedToZeroTwoSection (T : Finset K) : TwoSectionData K[X] where
  s0 := protectedToZeroPolynomial T
  s1 := 1
  span_top := by
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : K[X]) ∈ ({protectedToZeroPolynomial T, 1} : Set K[X]) := by simp
    exact Ideal.subset_span h1
  s0_ne_zero := protectedToZeroPolynomial_ne_zero T
  s1_ne_zero := one_ne_zero

/-- s1 = 1 avoids every point of the zero divisor D_T of s0. -/
theorem protectedToZero_s1_avoids {T : Finset K} {t : K} (ht : t ∈ T) :
    Polynomial.eval t (protectedToZeroTwoSection T).s1 ≠ 0 := by
  show Polynomial.eval t (1 : K[X]) ≠ 0
  simp

#print axioms eval_protectedToZero_eq_zero_iff
#print axioms protectedToZeroPolynomial_ne_zero
#print axioms rootMultiplicity_protectedToZero_of_mem
#print axioms protectedToZeroTwoSection
#print axioms not_both_mem_of_span_top
end LeanFormal.IUT.XiFPaper.Mzk1G1TwoSectionDataActual
