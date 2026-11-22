/-
Copyright (c) 2026 The IUT/ABC formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-! # S1466: degree and separable degree layer (Mathlib v4.32.2)

This ports the definitional and arithmetic part of Tau Ceti's
`Isogeny/Degree.lean`, `Isogeny/Separability.lean`, and
`MulByInt/Degree.lean` that is available in Mathlib v4.32.2:

* `isogenyDegree` / `isogenySeparableDegree` / `isogenyInseparableDegree`
  for a function-field embedding;
* `sepDeg * insepDeg = degree`;
* `sepDeg = degree` in the separable case;
* the actual arithmetic degree
  `[F(x) : F(Φ_n/ΨSq_n)] = n.natAbs ^ 2` from `IsCoprime (Φ_n) (ΨSq_n)`.

The actual `[n]` function-field isogeny and its separability are not
constructed in Mathlib v4.32.2; their exact first fields are recorded in the
report.  No `sorry`, `axiom`, or fake isogeny is used. -/

noncomputable section
open Polynomial

namespace WeierstrassCurve

variable {F : Type*} [Field F]

/-! ## 1. The pullback of the affine coordinate under `[n]` -/

/-- The rational function `Φ_n / ΨSq_n` in `F(x)`. -/
noncomputable def mulByIntX (W : WeierstrassCurve F) (n : ℤ) : RatFunc F :=
  algebraMap F[X] (RatFunc F) (W.Φ n) / algebraMap F[X] (RatFunc F) (W.ΨSq n)

/-- The subfield `F(Φ_n/ΨSq_n)` of `F(x)`. -/
noncomputable def mulByIntXRange (W : WeierstrassCurve F) (n : ℤ) :
    IntermediateField F (RatFunc F) :=
  IntermediateField.adjoin F {mulByIntX W n}

/-! ## 2. Arithmetic degree: `[F(x) : F(Φ_n/ΨSq_n)] = n ^ 2` -/

/-- **Arithmetic degree.**  If `Φ_n` and `ΨSq_n` are coprime, the quotient
`Φ_n/ΨSq_n` is in lowest terms and
`[F(x) : F(Φ_n/ΨSq_n)] = n.natAbs ^ 2`. -/
theorem finrank_adjoin_mulByIntX (W : WeierstrassCurve F) {n : ℤ}
    (hn : n ≠ 0) (hcop : IsCoprime (W.Φ n) (W.ΨSq n)) :
    Module.finrank (IntermediateField.adjoin F {mulByIntX W n}) (RatFunc F) =
      n.natAbs ^ 2 := by
  classical
  have hΦpos : 0 < (W.Φ n).natDegree := by
    rw [W.natDegree_Φ n]
    exact pow_pos (Int.natAbs_pos.mpr hn) 2
  have hΨ : W.ΨSq n ≠ 0 := by
    intro h
    have hunit : IsUnit (W.Φ n) := isCoprime_zero_right.mp (h ▸ hcop)
    exact hΦpos.ne' (natDegree_eq_zero_of_isUnit hunit)
  have hgu : IsUnit (gcd (W.Φ n) (W.ΨSq n)) :=
    gcd_isUnit_iff_isRelPrime.mpr hcop.isRelPrime
  obtain ⟨c, hc, hgcd⟩ := Polynomial.isUnit_iff.mp hgu
  have hcinv : c⁻¹ ≠ 0 := inv_ne_zero hc.ne_zero
  rw [mulByIntX, RatFunc.finrank_eq_max_natDegree, RatFunc.num_div,
    RatFunc.denom_div _ hΨ]
  set g := gcd (W.Φ n) (W.ΨSq n)
  have hΨdiv : W.ΨSq n / g ≠ 0 := by
    rw [← hgcd, Polynomial.div_C]
    exact mul_ne_zero hΨ (Polynomial.C_ne_zero.mpr hcinv)
  have hlc : ((W.ΨSq n / g).leadingCoeff)⁻¹ ≠ 0 :=
    inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hΨdiv)
  have hΦnd : (Polynomial.C ((W.ΨSq n / g).leadingCoeff)⁻¹ *
      (W.Φ n / g)).natDegree = (W.Φ n).natDegree := by
    rw [Polynomial.natDegree_C_mul hlc, ← hgcd, Polynomial.div_C,
      Polynomial.natDegree_mul_C hcinv]
  have hΨnd : (Polynomial.C ((W.ΨSq n / g).leadingCoeff)⁻¹ *
      (W.ΨSq n / g)).natDegree = (W.ΨSq n).natDegree := by
    rw [Polynomial.natDegree_C_mul hlc, ← hgcd, Polynomial.div_C,
      Polynomial.natDegree_mul_C hcinv]
  rw [hΦnd, hΨnd, W.natDegree_Φ n]
  exact max_eq_left ((W.natDegree_ΨSq_le n).trans (Nat.sub_le _ _))

/-! ## 3. Degree, separable degree, inseparable degree -/

/-- Degree of a function-field embedding: the dimension of the target over
the image of the pullback. -/
noncomputable def isogenyDegree {W₁ W₂ : WeierstrassCurve F}
    (f : W₁.toAffine.FunctionField →ₐ[F] W₂.toAffine.FunctionField) : ℕ :=
  Module.finrank f.fieldRange W₂.toAffine.FunctionField

/-- Separable degree of a function-field embedding. -/
noncomputable def isogenySeparableDegree {W₁ W₂ : WeierstrassCurve F}
    (f : W₁.toAffine.FunctionField →ₐ[F] W₂.toAffine.FunctionField) : ℕ :=
  Field.finSepDegree f.fieldRange W₂.toAffine.FunctionField

/-- Inseparable degree of a function-field embedding. -/
noncomputable def isogenyInseparableDegree {W₁ W₂ : WeierstrassCurve F}
    (f : W₁.toAffine.FunctionField →ₐ[F] W₂.toAffine.FunctionField) : ℕ :=
  Field.finInsepDegree f.fieldRange W₂.toAffine.FunctionField

/-- `sepDeg * insepDeg = degree`. -/
theorem isogenySeparableDegree_mul_inseparableDegree
    {W₁ W₂ : WeierstrassCurve F}
    (f : W₁.toAffine.FunctionField →ₐ[F] W₂.toAffine.FunctionField) :
    isogenySeparableDegree f * isogenyInseparableDegree f =
      isogenyDegree f :=
  Field.finSepDegree_mul_finInsepDegree _ _

/-- In the separable case, `sepDeg = degree`. -/
theorem isogenySeparableDegree_eq_degree_of_isSeparable
    {W₁ W₂ : WeierstrassCurve F}
    (f : W₁.toAffine.FunctionField →ₐ[F] W₂.toAffine.FunctionField)
    [Algebra.IsSeparable f.fieldRange W₂.toAffine.FunctionField] :
    isogenySeparableDegree f = isogenyDegree f := by
  rw [isogenySeparableDegree, isogenyDegree,
    Field.finSepDegree_eq_finrank_of_isSeparable]

/-- If the degree is `n.natAbs ^ 2` and the extension is separable, then the
separable degree is `n.natAbs ^ 2`.  This is the exact `sepDeg[n] = n^2`
shape once the `[n]` degree and separability are supplied. -/
theorem isogenySeparableDegree_eq_natAbs_sq_of_degree
    {W₁ W₂ : WeierstrassCurve F} {n : ℤ}
    (f : W₁.toAffine.FunctionField →ₐ[F] W₂.toAffine.FunctionField)
    (hdeg : isogenyDegree f = n.natAbs ^ 2)
    [Algebra.IsSeparable f.fieldRange W₂.toAffine.FunctionField] :
    isogenySeparableDegree f = n.natAbs ^ 2 := by
  rw [isogenySeparableDegree_eq_degree_of_isSeparable, hdeg]

end WeierstrassCurve

#print axioms WeierstrassCurve.finrank_adjoin_mulByIntX
#print axioms WeierstrassCurve.isogenySeparableDegree_mul_inseparableDegree
#print axioms WeierstrassCurve.isogenySeparableDegree_eq_natAbs_sq_of_degree

end
