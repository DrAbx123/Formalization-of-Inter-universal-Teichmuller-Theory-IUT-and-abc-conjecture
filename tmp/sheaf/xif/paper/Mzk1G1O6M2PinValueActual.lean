/- O6 / M2 pin value interface (route 4.3 L304-317; retry).

Reuse: Mzk1G1O6M2PinGeneralActual.pinMeasure_lex_of_reduction (DONE 14:06:47).
This file gives henry's P2 interface: degree decrease for f(alpha), derivative-root case,
orbit->0, and the Cauchy coefficient bound / beta-avoidance.
-/
import tmp.sheaf.xif.paper.Mzk1G1O6M2PinGeneralActual
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
noncomputable section
open Polynomial IntermediateField
namespace LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinValueActual

/-- a) degree comparison: deg minpoly(p(alpha)) <= deg minpoly(alpha). -/
theorem natDegree_minpoly_eval_le {α : ℂ} (hα : IsIntegral ℚ α) (p : ℚ[X]) :
    (minpoly ℚ ((p.map (algebraMap ℚ ℂ)).eval α)).natDegree ≤ (minpoly ℚ α).natDegree := by
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({α} : Set ℂ)
  let L : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({(p.map (algebraMap ℚ ℂ)).eval α} : Set ℂ)
  have hpK : (p.map (algebraMap ℚ ℂ)).eval α ∈ K := by
    have haeval : (p.map (algebraMap ℚ ℂ)).eval α = aeval α p := by
      simp only [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.eval_map]
    have hle : Algebra.adjoin ℚ ({α} : Set ℂ) ≤ K.toSubalgebra := by
      rw [Algebra.adjoin_le_iff]
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact (IntermediateField.subset_adjoin _ _ (Set.mem_singleton α))
    have hmem : aeval α p ∈ Algebra.adjoin ℚ ({α} : Set ℂ) := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]
      exact ⟨p, rfl⟩
    rw [haeval]
    exact hle hmem
  have hLK : L ≤ K := IntermediateField.adjoin_le_iff.mpr (by
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact hpK)
  haveI : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional hα
  have hLK_fin : Module.finrank ℚ L ≤ Module.finrank ℚ K :=
    IntermediateField.finrank_le_of_le_right hLK
  have hLintK : IsIntegral ℚ (⟨(p.map (algebraMap ℚ ℂ)).eval α, hpK⟩ : K) :=
    Algebra.IsIntegral.isIntegral _
  have hLint : IsIntegral ℚ ((p.map (algebraMap ℚ ℂ)).eval α) := by
    have := hLintK.algebraMap (A := K) (B := ℂ)
    simpa using this
  rw [IntermediateField.adjoin.finrank hLint, IntermediateField.adjoin.finrank hα] at hLK_fin
  exact hLK_fin

/-- b) derivative-root case: if beta is a root of f' and deg f = d >= 2, then
deg minpoly(f(beta)) <= d - 1. -/
theorem natDegree_minpoly_eval_le_derivative
    {f : ℚ[X]} {β : ℂ} (hm : f.Monic) (hd : 2 ≤ f.natDegree)
    (hβ : aeval β f.derivative = 0) :
    (minpoly ℚ ((f.map (algebraMap ℚ ℂ)).eval β)).natDegree ≤ f.natDegree - 1 := by
  have hder_ne : f.derivative ≠ 0 := by
    intro h
    have hdeg : f.derivative.natDegree = f.natDegree - 1 := by
      simpa using Polynomial.natDegree_derivative
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  have hder_deg : f.derivative.natDegree ≠ 0 := by
    intro h0
    have hdeg : f.derivative.natDegree = f.natDegree - 1 := by
      simpa using Polynomial.natDegree_derivative
    rw [h0] at hdeg
    omega
  have hβalg : IsAlgebraic ℚ β := IsAlgebraic.of_aeval f.derivative hder_deg hβ
  have hβint : IsIntegral ℚ β := hβalg.isIntegral
  have hβdeg : (minpoly ℚ β).natDegree ≤ f.natDegree - 1 := by
    have hdvd : minpoly ℚ β ∣ f.derivative := minpoly.dvd ℚ β hβ
    have hle := Polynomial.natDegree_le_of_dvd hdvd hder_ne
    simpa [Polynomial.natDegree_derivative] using hle
  exact (natDegree_minpoly_eval_le hβint f).trans hβdeg

/-- c) orbit case: a conjugate of alpha maps to 0. -/
theorem eval_eq_zero_of_isConjRoot {α β : ℂ} (h : IsConjRoot ℚ α β) :
    (minpoly ℚ α).eval β = 0 := by
  have h' := IsConjRoot.aeval_eq_zero h
  simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using h'

/-- c) orbit value has degree 1. -/
theorem natDegree_minpoly_eval_eq_one_of_isConjRoot {α β : ℂ}
    (h : IsConjRoot ℚ α β) :
    (minpoly ℚ ((minpoly ℚ α).eval β)).natDegree = 1 := by
  rw [eval_eq_zero_of_isConjRoot h]
  have h0 : (0 : ℂ) = algebraMap ℚ ℂ 0 := by simp
  rw [h0, minpoly.eq_X_sub_C']
  simp

/-- Explicit coefficient bound (B(d0) = sum of coefficient norms). -/
noncomputable def coeffBound (f : ℚ[X]) : ℝ :=
  ∑ i ∈ Finset.range (f.natDegree + 1), ‖(f.coeff i : ℂ)‖

/-- Cauchy coefficient bound on the unit disk. -/
theorem norm_eval_le_coeffBound {f : ℚ[X]} {s : ℂ} (hs : ‖s‖ ≤ 1) :
    ‖(f.map (algebraMap ℚ ℂ)).eval s‖ ≤ coeffBound f := by
  rw [Polynomial.eval_map]
  rw [Polynomial.eval_eq_sum_range]
  calc ‖∑ i ∈ Finset.range (f.natDegree + 1), algebraMap ℚ ℂ (f.coeff i) * s ^ i‖
      ≤ ∑ i ∈ Finset.range (f.natDegree + 1), ‖algebraMap ℚ ℂ (f.coeff i) * s ^ i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (f.natDegree + 1), ‖(f.coeff i : ℂ)‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, norm_pow]
        have hsi : ‖s‖ ^ i ≤ 1 := pow_le_one₀ (norm_nonneg s) hs
        calc ‖algebraMap ℚ ℂ (f.coeff i)‖ * ‖s‖ ^ i
            ≤ ‖algebraMap ℚ ℂ (f.coeff i)‖ * 1 :=
              mul_le_mul_of_nonneg_left hsi (norm_nonneg _)
          _ = ‖(f.coeff i : ℂ)‖ := by simp

/-- beta-avoidance: if S lies in the unit disk and |f(beta)| exceeds the coefficient bound,
then f(beta) is not in the image of S under f. -/
theorem pinValue_avoid {f : ℚ[X]} {S : Finset ℂ} {β : ℂ}
    (hS : ∀ s ∈ S, ‖s‖ ≤ 1) (hβ : coeffBound f < ‖(f.map (algebraMap ℚ ℂ)).eval β‖) :
    (f.map (algebraMap ℚ ℂ)).eval β ∉ S.image (fun s => (f.map (algebraMap ℚ ℂ)).eval s) := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨s, hs, hsf⟩
  have hle := norm_eval_le_coeffBound (f := f) (s := s) (hS s hs)
  rw [← hsf] at hle
  linarith

#print axioms natDegree_minpoly_eval_le
#print axioms natDegree_minpoly_eval_le_derivative
#print axioms eval_eq_zero_of_isConjRoot
#print axioms natDegree_minpoly_eval_eq_one_of_isConjRoot
#print axioms pinValue_avoid
end LeanFormal.IUT.XiFPaper.Mzk1G1O6M2PinValueActual
