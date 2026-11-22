/- G1-A §2.4 smooth 的代数核心：曲线环在 D(x) 上的 standard smooth presentation。
   route §2.4：添逆变量 z，把偏导 n x^{n-1} 变成单位，得到
   `ℚ[x,y,z]/(x^n+y^n-1, (n x^{n-1}) z - 1)` 的 submersive presentation；
   Jacobian 的行列式 = (n x^{n-1})^2，在商环中由关系 `(n x^{n-1}) z = 1` 成为单位；
   相对维数 card(vars) - card(rels) = 3 - 2 = 1。
   本文件实际构造该 presentation 并证明
   `Algebra.IsStandardSmoothOfRelativeDimension 1 ℚ (fermatModelRing n)`。
   不含 sorry/admit/axiom/PUnit/True/toy。 -/
import tmp.sheaf.xif.paper.Mzk1G1FermatAffineChartActual
import Mathlib.RingTheory.Extension.Presentation.Submersive
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

noncomputable section
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
namespace LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothAttemptActual
open MvPolynomial Matrix

/-! ### 局部化模型 -/

/-- 两条关系：`F = x^n+y^n-1`（i=0），`(n x^{n-1}) z - 1`（i=1）。 -/
noncomputable def fermatModelRel (n : Nat) (i : Fin 2) : MvPolynomial (Fin 3) ℚ :=
  if i = 0 then MvPolynomial.X 0 ^ n + MvPolynomial.X 1 ^ n - 1
  else ((n : MvPolynomial (Fin 3) ℚ) * MvPolynomial.X 0 ^ (n - 1)) *
    MvPolynomial.X 2 - 1

/-- 关系 ↦ 变量：`r1 ↦ x = X 0`，`r2 ↦ z = X 2`。 -/
def fermatModelIdx (i : Fin 2) : Fin 3 := if i = 0 then 0 else 2

theorem fermatModelIdx_injective : Function.Injective fermatModelIdx := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [fermatModelIdx] at h ⊢

theorem fermatModelRel_zero (n : Nat) :
    fermatModelRel n 0 = MvPolynomial.X 0 ^ n + MvPolynomial.X 1 ^ n - 1 := by
  simp [fermatModelRel]

theorem fermatModelRel_one (n : Nat) :
    fermatModelRel n 1 = ((n : MvPolynomial (Fin 3) ℚ) * MvPolynomial.X 0 ^ (n - 1)) *
      MvPolynomial.X 2 - 1 := by
  simp [fermatModelRel]

theorem fermatModelIdx_zero : fermatModelIdx 0 = (0 : Fin 3) := by
  simp [fermatModelIdx]

theorem fermatModelIdx_one : fermatModelIdx 1 = (2 : Fin 3) := by
  simp [fermatModelIdx, show ¬ ((1 : Fin 2) = 0) from by decide]

/-- 局部化模型环：`ℚ[x,y,z]/(F, (n x^{n-1}) z - 1)`。 -/
noncomputable abbrev fermatModelRing (n : Nat) : Type :=
  MvPolynomial (Fin 3) ℚ ⧸ Ideal.span (Set.range (fermatModelRel n))

/-- 该商环的 pre-submersive presentation（vars = Fin 3, rels = Fin 2）。 -/
noncomputable abbrev fermatModelPre (n : Nat) :
    Algebra.PreSubmersivePresentation ℚ (fermatModelRing n) (Fin 3) (Fin 2) :=
  Algebra.PreSubmersivePresentation.naive (v := fermatModelRel n) fermatModelIdx fermatModelIdx_injective

/-! ### Jacobian 计算 -/

theorem pderiv_X0_X1 : MvPolynomial.pderiv (0 : Fin 3)
    (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℚ) = 0 :=
  MvPolynomial.pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 0)

theorem pderiv_X0_X2 : MvPolynomial.pderiv (0 : Fin 3)
    (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℚ) = 0 :=
  MvPolynomial.pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 0)

theorem pderiv_X2_X0 : MvPolynomial.pderiv (2 : Fin 3)
    (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℚ) = 0 :=
  MvPolynomial.pderiv_X_of_ne (by decide : (0 : Fin 3) ≠ 2)

theorem pderiv_X2_X1 : MvPolynomial.pderiv (2 : Fin 3)
    (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℚ) = 0 :=
  MvPolynomial.pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 2)

theorem fermatModel_jacobiMatrix_zero_zero (n : Nat) :
    (fermatModelPre n).jacobiMatrix 0 0
      = (n : MvPolynomial (Fin 3) ℚ) * MvPolynomial.X 0 ^ (n - 1) := by
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_naive, fermatModelRel_zero, fermatModelIdx_zero]
  rw [Derivation.map_sub, Derivation.map_add,
    MvPolynomial.pderiv_pow, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_one]
  rw [MvPolynomial.pderiv_X_self, pderiv_X0_X1]
  ring

theorem fermatModel_jacobiMatrix_one_one (n : Nat) :
    (fermatModelPre n).jacobiMatrix 1 1
      = (n : MvPolynomial (Fin 3) ℚ) * MvPolynomial.X 0 ^ (n - 1) := by
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_naive, fermatModelRel_one, fermatModelIdx_one]
  rw [Derivation.map_sub, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_one,
    MvPolynomial.pderiv_X_self]
  rw [show (n : MvPolynomial (Fin 3) ℚ) = MvPolynomial.C (n : ℚ) from
    (MvPolynomial.C_eq_coe_nat (R := ℚ) n).symm]
  rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_pow, pderiv_X2_X0]
  ring

theorem fermatModel_jacobiMatrix_one_zero (n : Nat) :
    (fermatModelPre n).jacobiMatrix 1 0 = 0 := by
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_naive, fermatModelRel_zero, fermatModelIdx_one]
  rw [Derivation.map_sub, Derivation.map_add,
    MvPolynomial.pderiv_pow, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_one]
  rw [pderiv_X2_X0, pderiv_X2_X1]
  ring

theorem fermatModel_det (n : Nat) :
    (fermatModelPre n).jacobiMatrix.det
      = ((n : MvPolynomial (Fin 3) ℚ) * MvPolynomial.X 0 ^ (n - 1)) ^ 2 := by
  rw [Matrix.det_fin_two]
  rw [fermatModel_jacobiMatrix_zero_zero, fermatModel_jacobiMatrix_one_one,
    fermatModel_jacobiMatrix_one_zero]
  ring

/-! ### Jacobian 是单位 -/

theorem fermatModel_relation_mem (n : Nat) (i : Fin 2) :
    fermatModelRel n i ∈ Ideal.span (Set.range (fermatModelRel n)) :=
  Ideal.subset_span (Set.mem_range_self i)

theorem fermatModel_deriv_isUnit (n : Nat) :
    IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n)))
      ((n : MvPolynomial (Fin 3) ℚ) * MvPolynomial.X 0 ^ (n - 1))) := by
  have h0 : Ideal.Quotient.mk (Ideal.span (Set.range (fermatModelRel n)))
      (fermatModelRel n 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (fermatModel_relation_mem n 1)
  rw [fermatModelRel_one] at h0
  rw [map_sub, map_mul, map_one, sub_eq_zero] at h0
  exact IsUnit.of_mul_eq_one _ h0

theorem fermatModel_jacobian_isUnit (n : Nat) :
    IsUnit (fermatModelPre n).jacobian := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, fermatModel_det]
  rw [map_pow]
  exact (fermatModel_deriv_isUnit n).pow 2

/-! ### Standard smooth of relative dimension 1 -/

noncomputable def fermatModelPresentation (n : Nat) :
    Algebra.SubmersivePresentation ℚ (fermatModelRing n) (Fin 3) (Fin 2) where
  __ := fermatModelPre n
  jacobian_isUnit := fermatModel_jacobian_isUnit n

/-- route §2.4 smooth 的代数核心：局部化模型是相对维数 1 的 standard smooth ℚ-代数。 -/
theorem fermatModel_isStandardSmooth (n : Nat) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 ℚ (fermatModelRing n) := by
  refine Algebra.SubmersivePresentation.isStandardSmoothOfRelativeDimension
    (fermatModelPresentation n) ?_
  simp [Algebra.Presentation.dimension]

#print axioms fermatModelIdx_injective
#print axioms fermatModel_jacobiMatrix_zero_zero
#print axioms fermatModel_jacobiMatrix_one_one
#print axioms fermatModel_jacobiMatrix_one_zero
#print axioms fermatModel_det
#print axioms fermatModel_deriv_isUnit
#print axioms fermatModel_jacobian_isUnit
#print axioms fermatModel_isStandardSmooth

end LeanFormal.IUT.XiFPaper.Mzk1G1FermatSmoothAttemptActual