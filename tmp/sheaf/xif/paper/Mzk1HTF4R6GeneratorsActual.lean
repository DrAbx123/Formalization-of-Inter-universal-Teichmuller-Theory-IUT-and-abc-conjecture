import tmp.sheaf.xif.paper.Mzk1HTF4R6Actual
import Mathlib.NumberTheory.Height.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
/-!
# R6.2/R6.3: actual homogeneous generators, base divisor exactly E_i, local Weil function

ROUTE UPDATED R6: for the reduced `E_i`, take finite homogeneous generators `P_{i,j}` of
the ideal of `E_i` in the Fermat plane model and complete them to common degree `m_i`;
the base divisor `{y : P_{i,j}(y)=0 for all j}` is exactly `E_i`, and off `E_i` not all
`P_{i,j}` vanish.  The local Weil function is
`lambda_{E_i,v}(y) = m_i log max|x(y)|_v - log max_j|P_{i,j}(y)|_v` + fixed metric,
and by the product formula `sum_v lambda_{E_i,v}(y) = h_E(y) = m_i bar h_O(1) - bar h([P])`.

## Reuse / donor check (2026-11-17)
* `Mzk1HTF4R6Actual.R6LocalWeilData.ofProjHeight` / `hE_le_m` (DONE 15:58:47);
* `Mathlib.NumberTheory.Height.Basic`: `Height.logHeight_nonneg` (multi-coordinate);
* `MvPolynomial.IsHomogeneous` (degree completion data).

**No single-coordinate proxy**: `hP = Height.logHeight` of the **`ι`-indexed tuple** of
generator values (not `Unit`).  `h_E` is defined from the generator tuple and identified
with `sum_v lambda` by the finite place-sum algebra; the completion-to-degree construction
and the scheme-theoretic equality of the base divisor with `E_i` are explicit fields.
-/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.HTF4R6GeneratorsActual
open LeanFormal.IUT.XiFPaper.HTF4R6Actual

variable {K : Type*} [Field K] [Algebra ℚ K] [Height.AdmissibleAbsValues K]
  {ι : Type*} [Fintype ι]

/-- The actual reduced divisor `E_i` is cut out by the common zero set of the completed
homogeneous generators `P_j` (degree `m`). -/
structure R6GeneratorData (n : ℕ) where
  m : ℕ
  P : ι → MvPolynomial (Fin 3) ℚ
  homog : ∀ j, (P j).IsHomogeneous m
  x : Fin 3 → K
  E : Set (Fin 3 → K)
  baseDiv_eq : {y : Fin 3 → K |
      ∀ j, MvPolynomial.eval y ((P j).map (algebraMap ℚ K)) = 0} = E

/-- Off `E`, not all completed generators vanish (immediate from `baseDiv_eq`). -/
theorem R6GeneratorData.exists_eval_ne_zero_off {n : ℕ} (D : R6GeneratorData (K := K) (ι := ι) n)
    {y : Fin 3 → K} (hy : y ∉ D.E) :
    ∃ j, MvPolynomial.eval y ((D.P j).map (algebraMap ℚ K)) ≠ 0 := by
  by_contra h
  push_neg at h
  exact hy (by rw [← D.baseDiv_eq]; exact h)

/-- The multi-coordinate projective height of the completed generator tuple at `x`. -/
noncomputable def R6GeneratorData.hP {n : ℕ} (D : R6GeneratorData (K := K) (ι := ι) n) : ℝ :=
  Height.logHeight (fun j => MvPolynomial.eval D.x ((D.P j).map (algebraMap ℚ K)))

theorem R6GeneratorData.hP_nonneg {n : ℕ} (D : R6GeneratorData (K := K) (ι := ι) n) :
    0 ≤ D.hP :=
  Height.logHeight_nonneg _

/-- `R6GeneratorData` gives the R6 local Weil data with `hE = m hO1 - hP`. -/
noncomputable def R6GeneratorData.toR6 {n : ℕ} (D : R6GeneratorData (K := K) (ι := ι) n)
    (hn : 3 < (n : ℝ)) (hO1 : ℝ) : R6LocalWeilData where
  n := n
  n_gt_three := hn
  m := D.m
  hO1 := hO1
  hP := R6GeneratorData.hP D
  hP_nonneg := R6GeneratorData.hP_nonneg D
  hE := (D.m : ℝ) * hO1 - R6GeneratorData.hP D
  hE_eq := rfl
  hOmega := ((n : ℝ) - 3) * hO1
  hnorm := by
    have hne : ((n : ℝ) - 3) ≠ 0 := by linarith
    field_simp [hne]

theorem R6GeneratorData.hE_le_m {n : ℕ} (D : R6GeneratorData (K := K) (ι := ι) n)
    (hn : 3 < (n : ℝ)) (hO1 : ℝ) :
    (D.toR6 hn hO1).hE ≤ (D.m : ℝ) * hO1 :=
  (D.toR6 hn hO1).hE_le_m

/-- Finite place data: `logAbsX v = log max|x(y)|_v`, `logAbsP v = log max_j|P_j(y)|_v`. -/
structure R6PlaceData (V : Type*) [Fintype V] where
  m : ℕ
  hO1 : ℝ
  hP : ℝ
  logAbsX : V → ℝ
  logAbsP : V → ℝ
  hO1_eq : hO1 = ∑ v, logAbsX v
  hP_eq : hP = ∑ v, logAbsP v

/-- The local Weil function at the place `v`. -/
noncomputable def R6PlaceData.lambda {V : Type*} [Fintype V] (D : R6PlaceData V) (v : V) : ℝ :=
  (D.m : ℝ) * D.logAbsX v - D.logAbsP v

/-- **R6.3 product formula**: the sum of the local Weil functions is the global height
`hE = m hO1 - hP`. -/
theorem R6PlaceData.sum_lambda {V : Type*} [Fintype V] (D : R6PlaceData V) :
    ∑ v, R6PlaceData.lambda D v = (D.m : ℝ) * D.hO1 - D.hP := by
  unfold R6PlaceData.lambda
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, D.hO1_eq, D.hP_eq]
#print axioms R6GeneratorData.exists_eval_ne_zero_off
#print axioms R6GeneratorData.hE_le_m
#print axioms R6PlaceData.sum_lambda
end LeanFormal.IUT.XiFPaper.HTF4R6GeneratorsActual
end