import tmp.sheaf.xif.paper.Mzk1HTF4R6Actual
import tmp.sheaf.xif.paper.Mzk1HTF4R6GeneratorsActual
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic
/-!
# R6 crosswalk: projective completion, base divisor, per-place metric

Route IV:3172 (erratum): one-sided `h_E ≤ 2 (deg E / deg omega) h_omega + O(1)`,
via GenEll 1.4(ii)/1.6 — NOT the Tate local-height equality of GenEll 3.3.
Complete the homogeneous generators `P_j` (degree `d_j ≤ m`) to the complete family
`P_j * X_k^(m−d_j)` for `k=0,1,2`; at every projective point some `X_k` is a unit, so the
common zero set is `E_i`.
-/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.HTF4R6CrosswalkActual
open LeanFormal.IUT.XiFPaper.HTF4R6Actual
open LeanFormal.IUT.XiFPaper.HTF4R6GeneratorsActual

variable {K : Type*} [Field K] [Algebra ℚ K] {ι : Type*} [Fintype ι]

noncomputable def completeToDegreeFamily (m : ℕ) (d : ι → ℕ)
    (P : ι → MvPolynomial (Fin 3) ℚ) : ι × Fin 3 → MvPolynomial (Fin 3) ℚ :=
  fun jk => P jk.1 * (MvPolynomial.X jk.2) ^ (m - d jk.1)

theorem completeToDegreeFamily_isHomogeneous (m : ℕ) (d : ι → ℕ)
    (P : ι → MvPolynomial (Fin 3) ℚ) (hd : ∀ j, (P j).IsHomogeneous (d j))
    (hle : ∀ j, d j ≤ m) (jk : ι × Fin 3) :
    (completeToDegreeFamily m d P jk).IsHomogeneous m := by
  obtain ⟨j, k⟩ := jk
  unfold completeToDegreeFamily
  have hpow : ((MvPolynomial.X k : MvPolynomial (Fin 3) ℚ) ^ (m - d j)).IsHomogeneous (m - d j) :=
    MvPolynomial.isHomogeneous_X_pow (R := ℚ) k (m - d j)
  simpa [Nat.add_sub_of_le (hle j)] using (hd j).mul hpow

theorem completeToDegreeFamily_eval (m : ℕ) (d : ι → ℕ)
    (P : ι → MvPolynomial (Fin 3) ℚ) (y : Fin 3 → K) (jk : ι × Fin 3) :
    MvPolynomial.eval₂ (algebraMap ℚ K) y (completeToDegreeFamily m d P jk) =
      MvPolynomial.eval₂ (algebraMap ℚ K) y (P jk.1) * (y jk.2) ^ (m - d jk.1) := by
  simp [completeToDegreeFamily]

/-- Chart-X_0 completion (IUT chart form): Q_j = P_j * X_0^(m-d_j). -/
noncomputable def completeToDegree (m : Nat) (d : ι → Nat) (P : ι → MvPolynomial (Fin 3) ℚ) :
    ι → MvPolynomial (Fin 3) ℚ :=
  fun j => P j * (MvPolynomial.X (0 : Fin 3)) ^ (m - d j)

theorem completeToDegree_isHomogeneous (m : Nat) (d : ι → Nat)
    (P : ι → MvPolynomial (Fin 3) ℚ) (hd : ∀ j, (P j).IsHomogeneous (d j))
    (hle : ∀ j, d j ≤ m) (j : ι) :
    (completeToDegree m d P j).IsHomogeneous m := by
  unfold completeToDegree
  have hpow : ((MvPolynomial.X (0 : Fin 3) : MvPolynomial (Fin 3) ℚ) ^ (m - d j)).IsHomogeneous (m - d j) :=
    MvPolynomial.isHomogeneous_X_pow (0 : Fin 3) (m - d j)
  simpa [Nat.add_sub_of_le (hle j)] using (hd j).mul hpow

theorem completeToDegree_eval (m : Nat) (d : ι → Nat) (P : ι → MvPolynomial (Fin 3) ℚ)
    (y : Fin 3 → K) (j : ι) :
    MvPolynomial.eval₂ (algebraMap ℚ K) y (completeToDegree m d P j) =
      MvPolynomial.eval₂ (algebraMap ℚ K) y (P j) * (y 0) ^ (m - d j) := by
  simp [completeToDegree]

theorem baseDiv_completion_eq (m : Nat) (d : ι → Nat)
    (P : ι → MvPolynomial (Fin 3) ℚ) (y : Fin 3 → K) (hpt : ∃ k : Fin 3, y k ≠ 0) :
    (∀ jk, MvPolynomial.eval₂ (algebraMap ℚ K) y (completeToDegreeFamily m d P jk) = 0) ↔
      ∀ j, MvPolynomial.eval₂ (algebraMap ℚ K) y (P j) = 0 := by
  constructor
  · intro h j
    obtain ⟨k, hk⟩ := hpt
    have hx := h (j, k)
    rw [completeToDegreeFamily_eval] at hx
    exact (mul_eq_zero.mp hx).resolve_right (pow_ne_zero _ hk)
  · intro h jk
    rw [completeToDegreeFamily_eval, h jk.1, zero_mul]

structure R6SchemeBaseDivData (n : ℕ) where
  m : ℕ
  d : ι → ℕ
  P : ι → MvPolynomial (Fin 3) ℚ
  homog : ∀ j, (P j).IsHomogeneous (d j)
  hle : ∀ j, d j ≤ m
  E : Set (Fin 3 → K)
  baseDiv_eq : {y : Fin 3 → K | ∃ _hpt : ∃ k : Fin 3, y k ≠ 0,
      ∀ jk, MvPolynomial.eval₂ (algebraMap ℚ K) y (completeToDegreeFamily m d P jk) = 0} = E

structure R6MetricData (V : Type*) [Fintype V] where
  m : ℕ
  logAbsX : V → ℝ
  logAbsP : V → ℝ
  metric : V → ℝ

noncomputable def R6MetricData.lambda {V : Type*} [Fintype V] (D : R6MetricData V) (v : V) : ℝ :=
  (D.m : ℝ) * D.logAbsX v - D.logAbsP v + D.metric v

theorem R6MetricData.sum_lambda {V : Type*} [Fintype V] (D : R6MetricData V) :
    ∑ v, D.lambda v =
      (D.m : ℝ) * (∑ v, D.logAbsX v) - (∑ v, D.logAbsP v) + ∑ v, D.metric v := by
  simp [R6MetricData.lambda, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_sub_distrib]

#print axioms completeToDegree
#print axioms completeToDegree_isHomogeneous
#print axioms completeToDegree_eval
#print axioms completeToDegreeFamily_isHomogeneous
#print axioms completeToDegreeFamily_eval
#print axioms baseDiv_completion_eq
#print axioms R6SchemeBaseDivData
#print axioms R6MetricData
#print axioms R6MetricData.lambda
#print axioms R6MetricData.sum_lambda
end LeanFormal.IUT.XiFPaper.HTF4R6CrosswalkActual
end