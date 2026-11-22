import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Finsupp.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open Polynomial
open scoped BigOperators

namespace Probe1412

variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
variable (W : WeierstrassCurve.Affine F) [W.IsElliptic]

lemma exists_nonsingular_of_x (x : F) : ∃ y : F, W.Nonsingular x y := by
  classical
  let q : F[X] := X ^ 2 + C (W.a₁ * x + W.a₃) * X -
    C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)
  have hqdeg : q.degree = 2 := by
    change (X ^ 2 + C (W.a₁ * x + W.a₃) * X -
      C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) : F[X]).degree = 2
    compute_degree!
  have hdeg : q.degree ≠ 0 := by rw [hqdeg]; norm_num
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root q hdeg
  refine ⟨y, ?_⟩
  apply (WeierstrassCurve.Affine.equation_iff_nonsingular (W := W)).mp
  rw [WeierstrassCurve.Affine.equation_iff']
  have hy' : y ^ 2 + (W.a₁ * x + W.a₃) * y -
      (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
    simpa only [q, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.IsRoot.def] using hy
  linear_combination hy'

noncomputable def pointOfX (x : F) : W.Point :=
  WeierstrassCurve.Affine.Point.some x
    (Classical.choose (exists_nonsingular_of_x W x))
    (Classical.choose_spec (exists_nonsingular_of_x W x))

noncomputable def psiDivisor (n : ℤ) : W.Point →₀ ℤ :=
  (∑ x ∈ (W.preΨ n).roots.toFinset,
    ((W.preΨ n).rootMultiplicity x : ℤ) •
      (Finsupp.single (pointOfX W x) (1 : ℤ) +
        Finsupp.single (-(pointOfX W x)) (1 : ℤ))) -
    (2 * (W.preΨ n).natDegree : ℤ) • Finsupp.single (0 : W.Point) (1 : ℤ)

noncomputable def total {α : Type*} [DecidableEq α] (f : α →₀ ℤ) : ℤ :=
  f.sum (fun _ m => m)

@[simp] lemma total_zero {α : Type*} [DecidableEq α] :
    total (0 : α →₀ ℤ) = 0 := by simp [total]

@[simp] lemma total_single {α : Type*} [DecidableEq α] (a : α) (b : ℤ) :
    total (Finsupp.single a b) = b := by
  rw [total, Finsupp.sum_single_index]; rfl

lemma total_add {α : Type*} [DecidableEq α] (f g : α →₀ ℤ) :
    total (f + g) = total f + total g := by
  rw [total, Finsupp.sum_add_index']
  · rfl
  · intro a; rfl
  · intro a b c; ring

lemma total_smul {α : Type*} [DecidableEq α] (k : ℤ) (f : α →₀ ℤ) :
    total (k • f) = k * total f := by
  classical
  induction f using Finsupp.induction with
  | zero => simp
  | single_add a b f ha hf =>
      rw [smul_add, total_add, hf]
      have h1 : k • Finsupp.single a b = Finsupp.single a (k * b) := by
        rw [Finsupp.smul_single]; rfl
      rw [h1, total_single]
      have h2 : total (Finsupp.single a b) = b := total_single a b
      rw [h2]
      ring

example (n : ℤ) : total (psiDivisor W n) =
    (∑ x ∈ (W.preΨ n).roots.toFinset,
      ((W.preΨ n).rootMultiplicity x : ℤ) * 2) -
      2 * (W.preΨ n).natDegree := by
  classical
  rw [psiDivisor, total_add, total_smul, total_smul]
  · congr 1
    · rw [total, Finsupp.sum_finsetSum_index]
      · apply Finset.sum_congr rfl
        intro x hx
        rw [total, Finsupp.sum_smul_index]
        · rw [total, Finsupp.sum_add_index']
          · simp [total]
          · intro a; rfl
          · intro a b c; ring
        · intro a; rfl
      · intro a; rfl
      · intro a b c; ring
    · simp [total]

end Probe1412