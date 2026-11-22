import tmp.sheaf.xif.paper.RestatedLemma24InterfaceActual
import tmp.sheaf.xif.paper.Mzk1G1ProtectedToZeroMapActual
import tmp.sheaf.xif.paper.Mzk1G1TwoSectionDataActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1BelyiCVCompositionActual
open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProtectedToZeroMapActual

/-- A composite cannot have positive degree if one of the factors is constant;
hence both factors of a nonconstant composite are nonconstant. -/
theorem natDegree_ne_zero_of_comp {q r : Polynomial ℚ}
    (h : (r.comp q).natDegree ≠ 0) : q.natDegree ≠ 0 ∧ r.natDegree ≠ 0 := by
  constructor
  · intro hq
    have hqC : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hq
    rw [hqC] at h
    rw [Polynomial.comp_C, Polynomial.natDegree_C] at h
    exact h rfl
  · intro hr
    have hle : (r.comp q).natDegree ≤ r.natDegree * q.natDegree := Polynomial.natDegree_comp_le
    rw [hr, zero_mul] at hle
    exact h (Nat.le_zero.mp hle)

/-- **CV COMPOSITION LAW (proved)**: the critical values of a composite r.comp q are
contained in r applied to the critical values of q, together with the critical values
of r.  This is the chain-rule input for the B1 branch-set computation. -/
theorem criticalValuesOverC_comp_subset (q r : Polynomial ℚ) :
    criticalValuesOverC (r.comp q) ⊆
      (fun c => Polynomial.aeval c r) '' (criticalValuesOverC q) ∪ criticalValuesOverC r := by
  rintro c ⟨z, hne, hder, hval⟩
  rw [Polynomial.derivative_comp, Polynomial.aeval_mul, Polynomial.aeval_comp] at hder
  rcases mul_eq_zero.mp hder with h0 | h1
  · refine Set.mem_union_left _ ⟨Polynomial.aeval z q, ?_, ?_⟩
    · exact ⟨z, (natDegree_ne_zero_of_comp hne).1, h0, rfl⟩
    · exact (Polynomial.aeval_comp (x := z) (p := r) (q := q)).symm.trans hval
  · refine Set.mem_union_right _ ⟨Polynomial.aeval z q, (natDegree_ne_zero_of_comp hne).2, h1, ?_⟩
    exact (Polynomial.aeval_comp (x := z) (p := r) (q := q)).symm.trans hval

/-- The named composition-law gap of the Lemma 2.4 interface is DISCHARGED. -/
theorem cvCompositionLaw_proved : CVCompositionLawStatement :=
  fun q r => criticalValuesOverC_comp_subset q r

/-- The companion special-set preservation statement is discharged. -/
theorem specialSetPreservation_proved : SpecialSetPreservationStatement := by
  intro r h0 h1 c hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc h0 h1 ⊢
  rcases hc with rfl | rfl
  · exact h0
  · exact h1

/-! ## The first stage psi = [s0:s1] in its polynomial model

The protected-to-zero polynomial g = prod_{t in T} (X - t) is the affine model of
psi = [s0:s1]: its zero divisor is exactly D_T, every zero is simple, hence the whole
0-fiber is unramified over 0 (B2). -/

/-- ZERO IS NOT A CRITICAL VALUE OF THE FIRST STAGE: every point of the 0-fiber of the
protected-to-zero polynomial is a simple zero, so psi is unramified over 0. -/
theorem zero_not_critical_value {K : Type*} [Field K] [DecidableEq K]
    {T : Finset K} {x : K} (hx : Polynomial.eval x (protectedToZeroPolynomial T) = 0) :
    Polynomial.eval x (Polynomial.derivative (protectedToZeroPolynomial T)) ≠ 0 :=
  eval_derivative_protectedToZero_ne_zero
    ((LeanFormal.IUT.XiFPaper.Mzk1G1TwoSectionDataActual.eval_protectedToZero_eq_zero_iff).mp hx)

/-- The whole protected set T collapses to the SINGLE value q(0) under phi = q.comp g. -/
theorem comp_eval_on_T {T : Finset ℚ} {q : Polynomial ℚ} {t : ℚ} (ht : t ∈ T) :
    Polynomial.eval t (q.comp (protectedToZeroPolynomial T)) = Polynomial.eval 0 q := by
  rw [Polynomial.eval_comp, eval_protectedToZero_of_mem ht]

/-- B1, "must avoid" side: if q(0) is neither 0 nor 1, then phi = q.comp g sends the
whole protected set T outside the Belyi set {0,1,infinity} in P^1(Q). -/
theorem comp_T_avoids_specialSet {T : Finset ℚ} {q : Polynomial ℚ}
    (h0 : Polynomial.eval 0 q ≠ 0) (h1 : Polynomial.eval 0 q ≠ 1) {t : ℚ} (ht : t ∈ T) :
    polyEvalP1 (q.comp (protectedToZeroPolynomial T)) (P1Point.ofFinite t) ∉ specialSet ℚ := by
  have hval : Polynomial.eval t (q.comp (protectedToZeroPolynomial T)) = Polynomial.eval 0 q :=
    comp_eval_on_T ht
  have hmap : polyEvalP1 (q.comp (protectedToZeroPolynomial T)) (P1Point.ofFinite t) =
      P1Point.ofFinite (Polynomial.eval 0 q) := by
    show (some (Polynomial.eval t (q.comp (protectedToZeroPolynomial T))) : Option ℚ) =
      some (Polynomial.eval 0 q)
    rw [hval]
  intro hmem
  simp only [specialSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h
  · rw [hmap] at h
    exact P1Point.ofFinite_ne_infty (Polynomial.eval 0 q) h
  · rw [hmap] at h
    exact h0 (by simpa [P1Point.ofFinite] using h)
  · rw [hmap] at h
    exact h1 (by simpa [P1Point.ofFinite] using h)

/-- B1, branch side: if q maps all critical values of the first stage into {0,1} and q is
itself unramified away from {0,1}, then the composite phi = q.comp g has all critical
values over C inside {0,1} (and hence branch set inside {0,1,infinity}). -/
theorem comp_criticalValues_subset {T : Finset ℚ} {q : Polynomial ℚ}
    (hpsi : ∀ c ∈ criticalValuesOverC (protectedToZeroPolynomial T),
      Polynomial.aeval c q ∈ ({0, 1} : Set ℂ))
    (hq : criticalValuesOverC q ⊆ ({0, 1} : Set ℂ)) :
    criticalValuesOverC (q.comp (protectedToZeroPolynomial T)) ⊆ ({0, 1} : Set ℂ) := by
  intro c hc
  have hsub := criticalValuesOverC_comp_subset (protectedToZeroPolynomial T) q hc
  rcases hsub with h | h
  · obtain ⟨d, hd, rfl⟩ := h
    exact hpsi d hd
  · exact hq h

/-- B1 at the value level for the protected set: if q sends every psi-value of S into
{0,1}, then phi = q.comp g sends S into {0,1}. -/
theorem comp_preserves_values {S : Finset ℚ} {g q : Polynomial ℚ}
    (hS : ∀ s ∈ S, Polynomial.eval (Polynomial.eval s g) q = 0 ∨
      Polynomial.eval (Polynomial.eval s g) q = 1) :
    ∀ s ∈ S, Polynomial.eval s (q.comp g) = 0 ∨ Polynomial.eval s (q.comp g) = 1 := by
  intro s hs
  have hev : Polynomial.eval s (q.comp g) = Polynomial.eval (Polynomial.eval s g) q :=
    Polynomial.eval_comp
  rcases hS s hs with h | h
  · left
    rw [hev]
    exact h
  · right
    rw [hev]
    exact h

#print axioms cvCompositionLaw_proved
#print axioms specialSetPreservation_proved
#print axioms zero_not_critical_value
#print axioms comp_T_avoids_specialSet
#print axioms comp_criticalValues_subset
#print axioms comp_preserves_values
end LeanFormal.IUT.XiFPaper.Mzk1G1BelyiCVCompositionActual
