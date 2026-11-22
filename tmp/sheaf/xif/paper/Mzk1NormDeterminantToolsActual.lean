/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # P6 C-Norm: norm/determinant tools (C15), (C16) -/

/-
| field | value |
|---|---|
| Status | STATEMENT/PROVED skeletons: (C15) det = norm (re-export Mathlib); (C16) norm-power log relation proved |
| Reuse | `Mathlib/RingTheory/Norm/Defs.lean:64 norm_apply`, `:82 norm_eq_matrix_det`, `:100 norm_algebraMap` |
| GAP | (C13) Galois norm definition/functoriality not covered; product formula / restriction of scalars not covered; (C17)-(C20) interfaces in coord/P6-CNORM.md |
| Discipline | no sorry/axiom; no PUnit/True carrier |
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1NormDeterminantToolsActual

open Module

section DetNorm

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **(C15), linear-map form.**  The determinant of multiplication by `α` is the field norm.
Re-export of Mathlib `Algebra.norm_apply` (`Mathlib/RingTheory/Norm/Defs.lean:64`). -/
theorem norm_eq_det_lmul (α : L) :
    Algebra.norm K α = LinearMap.det (Algebra.lmul K L α) :=
  Algebra.norm_apply K α

/-- **(C15), matrix form.**  For any `K`-basis `b` of `L`, the norm is the determinant of
the left multiplication matrix.  Re-export of Mathlib `Algebra.norm_eq_matrix_det`
(`Mathlib/RingTheory/Norm/Defs.lean:82`). -/
theorem norm_eq_matrix_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K L) (α : L) :
    Algebra.norm K α = (Algebra.leftMulMatrix b α).det :=
  Algebra.norm_eq_matrix_det (R := K) (S := L) b α

end DetNorm

section NormPowerLog

variable {K L : Type*} [NormedField K] [Field L] [Algebra K L]
variable [Module.Free K L] [Module.Finite K L]

/-- **(C16).**  If `α ^ r = algebraMap K L q` with `r > 0` and `q ≠ 0`, then
`r * log ‖N_{L/K}(α)‖ = [L:K] * log ‖q‖`.

This is the norm/determinant/log compatibility behind the (C17)-(C20) interfaces:
taking `Algebra.norm K` gives `(N α)^r = q^[L:K]`, then apply `‖·‖` and `Real.log`.
Uses Mathlib `Algebra.norm_algebraMap` (`Norm/Defs.lean:100`). -/
theorem norm_pow_log_relation
    (r : ℕ) (hr : 0 < r) (α : L) (q : K)
    (hα : α ^ r = algebraMap K L q) (hq : q ≠ 0) :
    (r : ℝ) * Real.log ‖Algebra.norm K α‖ =
      (Module.finrank K L : ℝ) * Real.log ‖q‖ := by
  have hnorm : (Algebra.norm K α) ^ r = q ^ Module.finrank K L := by
    have h := congrArg (Algebra.norm K) hα
    simpa using h
  have hqpow : q ^ Module.finrank K L ≠ 0 := pow_ne_zero _ hq
  have hN : Algebra.norm K α ≠ 0 := by
    intro h0
    have hzero : (Algebra.norm K α) ^ r = 0 := by
      rw [h0]; exact zero_pow hr.ne'
    rw [hnorm] at hzero
    exact hqpow hzero
  have habs : ‖Algebra.norm K α‖ ^ r = ‖q‖ ^ Module.finrank K L := by
    calc ‖Algebra.norm K α‖ ^ r = ‖(Algebra.norm K α) ^ r‖ := (norm_pow _ _).symm
      _ = ‖q ^ Module.finrank K L‖ := by rw [hnorm]
      _ = ‖q‖ ^ Module.finrank K L := norm_pow _ _
  have hlog := congrArg Real.log habs
  rw [Real.log_pow, Real.log_pow] at hlog
  exact hlog

end NormPowerLog

section GaloisNorm

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- **(C13), product form.**  In a Galois extension, the norm is the product over the
Galois group: `algebraMap K L (N α) = ∏ σ : Gal(L/K), σ α`.
Re-export of Mathlib `Algebra.norm_eq_prod_automorphisms`
(`Mathlib/RingTheory/Norm/Transitivity.lean:272`). -/
theorem norm_galois_product (α : L) :
    algebraMap K L (Algebra.norm K α) = ∏ σ : Gal(L/K), σ α :=
  Algebra.norm_eq_prod_automorphisms K α

/-- **Norm functoriality (multiplicative).**  Re-export of `map_mul` for the monoid hom
`Algebra.norm K`. -/
theorem norm_mul (α β : L) :
    Algebra.norm K (α * β) = Algebra.norm K α * Algebra.norm K β :=
  map_mul _ _ _

/-- **Norm functoriality (powers).**  Re-export of `map_pow` for `Algebra.norm K`. -/
theorem norm_pow (α : L) (n : ℕ) :
    Algebra.norm K (α ^ n) = (Algebra.norm K α) ^ n :=
  map_pow _ _ _

end GaloisNorm
def cNormRows : List (String × String) :=
  [ ("norm_eq_det_lmul", "(C15) det(lmul) = norm (re-export Mathlib)") ,
    ("norm_eq_matrix_det", "(C15) matrix form (re-export Mathlib)") ,
    ("norm_pow_log_relation", "(C16) r*log||N alpha|| = [L:K]*log||q|| (PROVED)") ,
    ("norm_galois_product", "(C13) algebraMap(N alpha) = prod sigma alpha (re-export Mathlib)") ,
    ("norm_mul / norm_pow", "norm functoriality: multiplicative and powers (re-export map_mul/map_pow)") ,
    ("GAP-PRODUCT-FORMULA", "global product formula and restriction of scalars not covered") ]

theorem cNormRows_length : cNormRows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1NormDeterminantToolsActual