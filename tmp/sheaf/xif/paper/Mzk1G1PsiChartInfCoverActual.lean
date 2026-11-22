import tmp.sheaf.xif.paper.Mzk1G1PsiChartMapsActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartInfCoverActual
open AlgebraicGeometry Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual

variable (n : Nat)

/-- The reciprocal chart polynomial q = prod (1 - t r) is congruent to 1 modulo r. -/
theorem psiChartInfDenom_sub_one_mem (T : Finset ℚ) :
    psiChartInfDenom n T - 1 ∈ Ideal.span ({chartR n} : Set (R2 n)) := by
  induction T using Finset.induction_on with
  | empty =>
      have h : psiChartInfDenom n (∅ : Finset ℚ) = 1 := by simp [psiChartInfDenom]
      rw [h, sub_self]
      exact Ideal.zero_mem _
  | insert b s hb ih =>
      have hstep : psiChartInfDenom n (insert b s) =
          (1 - algebraMap ℚ (R2 n) b * chartR n) * psiChartInfDenom n s := by
        unfold psiChartInfDenom
        rw [Finset.prod_insert hb]
      rw [hstep]
      have hb1 : (1 - algebraMap ℚ (R2 n) b * chartR n) * psiChartInfDenom n s - 1 =
          (psiChartInfDenom n s - 1) +
            (algebraMap ℚ (R2 n) b * chartR n) * (-psiChartInfDenom n s) := by
        ring
      rw [hb1]
      refine Ideal.add_mem _ ih ?_
      refine Ideal.mul_mem_right _ _ ?_
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

/-- COVERAGE INPUT for the global two-chart construction of psi: on the second affine
Fermat chart the functions q = prod (1 - t r) and r generate the unit ideal.  Equivalently
the open D(q) contains the whole "infinity" locus r = 0, so the first chart together with
D(q) already covers Y_n. -/
theorem span_denom_chartR_eq_top (T : Finset ℚ) :
    Ideal.span ({psiChartInfDenom n T, chartR n} : Set (R2 n)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hq : psiChartInfDenom n T ∈ Ideal.span ({psiChartInfDenom n T, chartR n} : Set (R2 n)) :=
    Ideal.subset_span (by left; rfl)
  have hsub : psiChartInfDenom n T - 1 ∈
      Ideal.span ({psiChartInfDenom n T, chartR n} : Set (R2 n)) := by
    have h1 : psiChartInfDenom n T - 1 ∈ Ideal.span ({chartR n} : Set (R2 n)) :=
      psiChartInfDenom_sub_one_mem n T
    have hle : Ideal.span ({chartR n} : Set (R2 n)) ≤
        Ideal.span ({psiChartInfDenom n T, chartR n} : Set (R2 n)) := by
      rw [Ideal.span_le]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Ideal.subset_span (by right; rfl)
    exact hle h1
  have hone : (1 : R2 n) = psiChartInfDenom n T - (psiChartInfDenom n T - 1) := by ring
  rw [hone]
  exact Ideal.sub_mem _ hq hsub

/-- q and r have no common zero on the second chart: no prime contains both. -/
theorem no_common_zero_denom_chartR (T : Finset ℚ) (P : Ideal (R2 n)) [P.IsPrime] :
    ¬ (psiChartInfDenom n T ∈ P ∧ chartR n ∈ P) := by
  rintro ⟨h1, h2⟩
  have hle : Ideal.span ({psiChartInfDenom n T, chartR n} : Set (R2 n)) ≤ P := by
    rw [Ideal.span_le]
    rintro x (rfl | rfl)
    · exact h1
    · exact h2
  rw [span_denom_chartR_eq_top n T] at hle
  exact (inferInstance : P.IsPrime).ne_top (top_le_iff.mp hle)

#print axioms psiChartInfDenom_sub_one_mem
#print axioms span_denom_chartR_eq_top
#print axioms no_common_zero_denom_chartR
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartInfCoverActual
