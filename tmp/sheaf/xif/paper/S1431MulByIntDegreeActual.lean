/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.IntermediateField.ExtendRight
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# S1431: the degree and separable degree of multiplication by an integer

This file ports the degree conclusions of Tau Ceti's
`AlgebraicGeometry/EllipticCurve/Isogeny/MulByInt/Degree.lean` and
`AlgebraicGeometry/EllipticCurve/Isogeny/MulByInt/Separability.lean`
(Tau Ceti commit `df319cee080d8cab30699ff8ab3ed8d9347768aa`, Lean v4.36.0-rc1)
to Mathlib v4.32.2. Tau Ceti is not importable here, and none of its proof
closure is vendored: what is reproduced is the field-theoretic content of the
two files on the objects Mathlib v4.32.2 does provide.

## The mathematical content

For a Weierstrass curve `W` over a field `F`, the isogeny `[n]` pulls the
affine coordinate `x` back to the rational function `Φₙ / ΨSqₙ : F(x)`.
Its degree is the degree of the induced function-field extension. Two
computations give that degree:

* the **arithmetic half**: `[F(x) : F(Φₙ/ΨSqₙ)] = n ^ 2`, read off the
  numerator and denominator degrees by `RatFunc.finrank_eq_max_natDegree`;
* the **geometric half**: the tower `F(Φₙ/ΨSqₙ) ⊆ F(x) ⊆ F(W)`, in which
  the outer storey has degree two, so an embedding of function fields
  carrying the affine coordinate to `Φₙ/ΨSqₙ` has image of index `n ^ 2`.

Composing them gives `degree_mulByIntIsogeny`: any function-field embedding
whose pullback of the affine coordinate is `Φₙ/ΨSqₙ` has degree `n ^ 2`,
the conclusion of Tau Ceti's `degree_mulByIntIsogeny`. In the separable case
the separable degree is the whole degree, giving
`separableDegree_mulByIntIsogeny = n ^ 2`, the conclusion of Tau Ceti's
`separableDegree_mulByIntIsogeny`.

## The two exact first fields

Two mathematical inputs of the Tau Ceti files are not available in Mathlib
v4.32.2 and are therefore explicit hypotheses, not axioms and not `sorry`:

* `IsCoprime (W.Φ n) (W.ΨSq n)`, the input to the arithmetic half. It is Tau
  Ceti's `WeierstrassCurve.isCoprime_Φ_ΨSq`, proved there through the
  `ZSMul` closure (`zsmul_point_eq_smulEval`, `nonsingular_smulEval`,
  `Jacobian.X_ne_zero_of_Z_eq_zero`). That closure needs the elliptic-net
  theorem `IsEllipticNet (normEDS b c d)`, which Mathlib v4.32.2 records as a
  TODO; see `S1411ZSMulBridgeActual` in this tree. Without coprimality the
  quotient `Φₙ/ΨSqₙ` is not in lowest terms and the degree can drop.
* `Algebra.IsSeparable f.fieldRange W.FunctionField`, the input separating the
  two parts of the degree. Tau Ceti proves it for `[n]` from the invariant
  differential (`[n]` scales `ω` by `n`); Mathlib v4.32.2 has no invariant
  differential on a Weierstrass function field, so that criterion is not
  ported here. It is not assumed anywhere unconditionally.

Everything else is proved: the function-field tower, `[F(W) : F(x)] = 2`, the
arithmetic half from coprimality, and the field-theoretic factorisation
`separableDegree * inseparableDegree = degree`.

## Main results

* `WeierstrassCurve.mulByIntX`: the pullback of the affine coordinate under `[n]`.
* `WeierstrassCurve.finrank_adjoin_mulByIntX`: `[F(x) : F(Φₙ/ΨSqₙ)] = n ^ 2`.
* `WeierstrassCurve.finrank_fieldRange_of_apply_X_eq_mulByIntX`: the degree
  of any function-field embedding whose pullback of `x` is `Φₙ/ΨSqₙ` is `n ^ 2`.
* `WeierstrassCurve.degree_mulByIntIsogeny`: the same, in the isogeny-degree form.
* `WeierstrassCurve.separableDegree_mulByIntIsogeny`: in the separable case the
  separable degree is `n ^ 2`.
* `WeierstrassCurve.isogenySeparableDegree_mul_inseparableDegree`: the general
  field-theoretic factorisation of an isogeny degree.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009],
  III.5.4 and III.6.4(a).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section

open Polynomial

namespace WeierstrassCurve

variable {F : Type*} [Field F]

/-! ## 1. The function field as a quadratic extension of the rational function field -/

/-- The affine coordinate ring is finite over the polynomial ring, from Mathlib's power basis. -/
local instance moduleFinite_coordinateRing (W : WeierstrassCurve F) :
    Module.Finite F[X] W.toAffine.CoordinateRing :=
  Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine)

/-- The affine coordinate ring has rank two over the polynomial ring. -/
theorem finrank_coordinateRing (W : WeierstrassCurve F) :
    Module.finrank F[X] W.toAffine.CoordinateRing = 2 :=
  (Module.finrank_eq_card_basis
    (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine)).trans (by simp)

/-- The polynomial defining the coordinate ring has nonzero degree, so the
structure map from `F[X]` is injective. -/
private theorem polynomial_degree_ne_zero (W : WeierstrassCurve F) :
    W.toAffine.polynomial.degree ≠ 0 := by
  rw [Polynomial.degree_eq_natDegree W.toAffine.monic_polynomial.ne_zero,
    WeierstrassCurve.Affine.natDegree_polynomial]
  simp

/-- The polynomial ring embeds in the coordinate ring. -/
local instance faithfulSMul_polynomial_coordinateRing (W : WeierstrassCurve F) :
    FaithfulSMul F[X] W.toAffine.CoordinateRing := by
  rw [faithfulSMul_iff_algebraMap_injective]
  simpa using AdjoinRoot.of.injective_of_degree_ne_zero (polynomial_degree_ne_zero W)

/-- The polynomial ring embeds in the function field. -/
local instance faithfulSMul_polynomial_functionField (W : WeierstrassCurve F) :
    FaithfulSMul F[X] W.toAffine.FunctionField := by
  rw [faithfulSMul_iff_algebraMap_injective,
    IsScalarTower.algebraMap_eq F[X] W.toAffine.CoordinateRing W.toAffine.FunctionField]
  exact (IsFractionRing.injective W.toAffine.CoordinateRing W.toAffine.FunctionField).comp
    (by simpa using AdjoinRoot.of.injective_of_degree_ne_zero (polynomial_degree_ne_zero W))

/-- The fraction ring of `F[X]` acts on the function field through Mathlib's
`FractionRing.liftAlgebra`.  Local, because it is a diamond when the two fraction
fields coincide. -/
local instance algebra_fractionRing_functionField (W : WeierstrassCurve F) :
    Algebra (FractionRing F[X]) W.toAffine.FunctionField :=
  FractionRing.liftAlgebra F[X] W.toAffine.FunctionField

/-- The scalar tower `F[X] ⊆ Frac F[X] ⊆ F(W)`. -/
local instance isScalarTower_fractionRing_functionField (W : WeierstrassCurve F) :
    IsScalarTower F[X] (FractionRing F[X]) W.toAffine.FunctionField :=
  FractionRing.isScalarTower_liftAlgebra F[X] W.toAffine.FunctionField

/-- The scalar tower `F ⊆ Frac F[X] ⊆ F(W)`. -/
local instance isScalarTower_base_fractionRing_functionField (W : WeierstrassCurve F) :
    IsScalarTower F (FractionRing F[X]) W.toAffine.FunctionField :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply F F[X] (FractionRing F[X]),
      ← IsScalarTower.algebraMap_apply F[X] (FractionRing F[X]) W.toAffine.FunctionField]
    exact IsScalarTower.algebraMap_apply F F[X] W.toAffine.FunctionField x

/-- The rational function field acts on the function field, by transferring the
`FractionRing F[X]`-algebra structure across `RatFunc.toFractionRingAlgEquiv`.
Local, because it is a diamond when the two fraction fields coincide. -/
local instance algebra_ratFunc_functionField (W : WeierstrassCurve F) :
    Algebra (RatFunc F) W.toAffine.FunctionField :=
  RingHom.toAlgebra
    ((algebraMap (FractionRing F[X]) W.toAffine.FunctionField).comp
      (RatFunc.toFractionRingAlgEquiv (K := F) (R := F[X])).toRingHom)

/-- The scalar tower `F ⊆ F(x) ⊆ F(W)`. -/
local instance isScalarTower_base_ratFunc_functionField (W : WeierstrassCurve F) :
    IsScalarTower F (RatFunc F) W.toAffine.FunctionField := by
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  change algebraMap F W.toAffine.FunctionField x =
    algebraMap (FractionRing F[X]) W.toAffine.FunctionField
      ((RatFunc.toFractionRingAlgEquiv (K := F) (R := F[X])) (algebraMap F (RatFunc F) x))
  rw [IsScalarTower.algebraMap_apply F F[X] (RatFunc F),
    (RatFunc.toFractionRingAlgEquiv (K := F) (R := F[X])).commutes,
    ← IsScalarTower.algebraMap_apply F[X] (FractionRing F[X]) W.toAffine.FunctionField]
  exact IsScalarTower.algebraMap_apply F F[X] W.toAffine.FunctionField x

/-- The scalar tower `F[X] ⊆ F(x) ⊆ F(W)`. -/
local instance isScalarTower_poly_ratFunc_functionField (W : WeierstrassCurve F) :
    IsScalarTower F[X] (RatFunc F) W.toAffine.FunctionField := by
  refine IsScalarTower.of_algebraMap_eq fun p => ?_
  change algebraMap F[X] W.toAffine.FunctionField p =
    algebraMap (FractionRing F[X]) W.toAffine.FunctionField
      ((RatFunc.toFractionRingAlgEquiv (K := F) (R := F[X])) (algebraMap F[X] (RatFunc F) p))
  rw [(RatFunc.toFractionRingAlgEquiv (K := F) (R := F[X])).commutes,
    ← IsScalarTower.algebraMap_apply F[X] (FractionRing F[X]) W.toAffine.FunctionField]

section FunctionField

variable (W : WeierstrassCurve F)

/-- The defining equation of `IntermediateField.extendRight`, which Mathlib
v4.32.2 states only as the definition. -/
theorem extendRight_eq_map (E : IntermediateField F (RatFunc F)) :
    E.extendRight W.toAffine.FunctionField =
      E.map (IsScalarTower.toAlgHom F (RatFunc F) W.toAffine.FunctionField) := rfl

/-- **The function field is a quadratic extension of the rational function field.**
Mathlib's `Algebra.IsAlgebraic.finrank_of_isFractionRing` applied to the fraction
rings of `F[X]` and `W.CoordinateRing`, whose ranks agree by Mathlib's power
basis. -/
theorem finrank_functionField :
    Module.finrank (RatFunc F) W.toAffine.FunctionField = 2 := by
  rw [Algebra.IsAlgebraic.finrank_of_isFractionRing F[X] (RatFunc F)
    W.toAffine.CoordinateRing W.toAffine.FunctionField]
  exact finrank_coordinateRing W

/-- The copy of `F(x)` inside `F(W)`, as an intermediate field. -/
noncomputable def ratFuncRange : IntermediateField F W.toAffine.FunctionField :=
  (IsScalarTower.toAlgHom F (RatFunc F) W.toAffine.FunctionField).fieldRange

/-- The copy of `F(x)` is the image of the whole rational function field. -/
theorem ratFuncRange_eq_map :
    ratFuncRange W = (⊤ : IntermediateField F (RatFunc F)).map
      (IsScalarTower.toAlgHom F (RatFunc F) W.toAffine.FunctionField) :=
  AlgHom.fieldRange_eq_map _

/-- **The degree above the range of a field embedding equals the degree above its
source.** Ported from Tau Ceti's `AlgHom.finrank_fieldRange`; Mathlib v4.32.2 has
the ingredients (`AlgHom.equivFieldRange`, `Algebra.finrank_eq_of_equiv_equiv`)
but not this composition. -/
theorem finrank_fieldRange {K L : Type*} [Field K] [Field L]
    [Algebra F K] [Algebra F L] (f : K →ₐ[F] L) [Algebra K L]
    (h : ∀ z, algebraMap K L z = f z) :
    Module.finrank f.fieldRange L = Module.finrank K L := by
  have hsquare : (algebraMap f.fieldRange L).comp f.equivFieldRange.toRingEquiv.toRingHom =
      (RingEquiv.refl L).toRingHom.comp (algebraMap K L) := by
    ext z
    exact (AlgHom.equivFieldRange_apply_coe f z).trans (h z).symm
  exact (Algebra.finrank_eq_of_equiv_equiv f.equivFieldRange.toRingEquiv (RingEquiv.refl L)
    hsquare).symm

/-- **`[F(W) : F(x)] = 2`** for the copy of the rational function field inside
the function field. -/
theorem finrank_ratFuncRange :
    Module.finrank (ratFuncRange W) W.toAffine.FunctionField = 2 := by
  rw [ratFuncRange]
  exact (finrank_fieldRange
    (IsScalarTower.toAlgHom F (RatFunc F) W.toAffine.FunctionField)
    (fun z => (IsScalarTower.toAlgHom_apply F (RatFunc F)
      W.toAffine.FunctionField z).symm)).trans (finrank_functionField W)

/-- **The image of `F(W)` has degree two over the image of `F(x)`.** -/
theorem relfinrank_map_ratFuncRange_fieldRange {M : Type*} [Field M] [Algebra F M]
    (f : W.toAffine.FunctionField →ₐ[F] M) :
    IntermediateField.relfinrank ((ratFuncRange W).map f) f.fieldRange = 2 := by
  rw [AlgHom.fieldRange_eq_map, IntermediateField.relfinrank_map_map,
    IntermediateField.relfinrank_top_right, finrank_ratFuncRange]

/-- Any subfield of `F(x)` sits inside `F(x)` in `F(W)`. -/
theorem extendRight_le_ratFuncRange (E : IntermediateField F (RatFunc F)) :
    E.extendRight W.toAffine.FunctionField ≤ ratFuncRange W := by
  rw [ratFuncRange, AlgHom.fieldRange_eq_map, extendRight_eq_map]
  exact IntermediateField.map_mono _ le_top

/-- **`[F(x) : E]`, read inside `F(W)`, is the degree it has inside `F(x)`.** -/
theorem relfinrank_extendRight (E : IntermediateField F (RatFunc F)) :
    IntermediateField.relfinrank (E.extendRight W.toAffine.FunctionField) (ratFuncRange W) =
      Module.finrank E (RatFunc F) := by
  rw [ratFuncRange, AlgHom.fieldRange_eq_map, extendRight_eq_map,
    IntermediateField.relfinrank_map_map]
  exact IntermediateField.relfinrank_top_right E

/-- **`[F(W) : E] = 2 · [F(x) : E]`**: the inner storey contributes the degree
of `E` and the outer one contributes two. -/
theorem finrank_extendRight (E : IntermediateField F (RatFunc F)) :
    Module.finrank (E.extendRight W.toAffine.FunctionField) W.toAffine.FunctionField =
      2 * Module.finrank E (RatFunc F) := by
  rw [← IntermediateField.relfinrank_mul_finrank_top (extendRight_le_ratFuncRange W E),
    relfinrank_extendRight W E, finrank_ratFuncRange W, Nat.mul_comm]

/-- **The copy of `F(g)` inside `F(W)` is the image of the rational function
field of `W'`**, for a function-field embedding carrying the affine coordinate
of `W'` to `g`. -/
theorem extendRight_adjoin_eq_map_ratFuncRange {W' : WeierstrassCurve F} {g : RatFunc F}
    (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (hf : f (algebraMap F[X] W'.toAffine.FunctionField X) =
      algebraMap (RatFunc F) W.toAffine.FunctionField g) :
    (IntermediateField.adjoin F {g}).extendRight W.toAffine.FunctionField =
      (ratFuncRange W').map f := by
  have hX : algebraMap (RatFunc F) W'.toAffine.FunctionField RatFunc.X =
      algebraMap F[X] W'.toAffine.FunctionField X := by
    rw [← RatFunc.algebraMap_X,
      IsScalarTower.algebraMap_apply F[X] (RatFunc F) W'.toAffine.FunctionField]
  rw [ratFuncRange, AlgHom.fieldRange_eq_map, IntermediateField.map_map,
    ← RatFunc.adjoin_X, extendRight_eq_map, IntermediateField.adjoin_map]
  simp only [IntermediateField.adjoin_map, Set.image_singleton, AlgHom.coe_comp,
    Function.comp_apply, IsScalarTower.toAlgHom_apply, hX, hf]

/-- **`[F(W) : f(F(W'))] = [F(x) : F(g)]`** for a function-field embedding
carrying the affine coordinate of `W'` to `g`. -/
theorem finrank_fieldRange_of_apply_X_eq {W' : WeierstrassCurve F} {g : RatFunc F}
    (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (hf : f (algebraMap F[X] W'.toAffine.FunctionField X) =
      algebraMap (RatFunc F) W.toAffine.FunctionField g) :
    Module.finrank f.fieldRange W.toAffine.FunctionField =
      Module.finrank (IntermediateField.adjoin F {g}) (RatFunc F) := by
  set E : IntermediateField F (RatFunc F) := IntermediateField.adjoin F {g} with hE
  have h : E.extendRight W.toAffine.FunctionField =
      (ratFuncRange W').map f := by
    rw [hE]
    exact extendRight_adjoin_eq_map_ratFuncRange W f hf
  have hle : E.extendRight W.toAffine.FunctionField ≤ f.fieldRange := by
    rw [h, AlgHom.fieldRange_eq_map]
    exact IntermediateField.map_mono _ le_top
  have hrel : IntermediateField.relfinrank
      (E.extendRight W.toAffine.FunctionField) f.fieldRange = 2 := by
    rw [h]
    exact relfinrank_map_ratFuncRange_fieldRange W' f
  have htower := IntermediateField.relfinrank_mul_finrank_top hle
  rw [hrel, finrank_extendRight W E] at htower
  exact Nat.eq_of_mul_eq_mul_left two_pos htower

end FunctionField

/-! ## 2. The pullback of the affine coordinate under `[n]` -/

variable (W : WeierstrassCurve F)

/-- **The pullback of the affine coordinate under `[n]`**: the rational function
`Φₙ / ΨSqₙ`, formed in `F(x)`. -/
noncomputable def mulByIntX (n : ℤ) : RatFunc F :=
  algebraMap F[X] (RatFunc F) (W.Φ n) / algebraMap F[X] (RatFunc F) (W.ΨSq n)

/-- The subfield `F(Φₙ/ΨSqₙ)` of `F(x)`. -/
noncomputable def mulByIntXRange (n : ℤ) : IntermediateField F (RatFunc F) :=
  IntermediateField.adjoin F {mulByIntX W n}

/-! ## 3. The arithmetic half: `[F(x) : F(Φₙ/ΨSqₙ)] = n ^ 2` -/

/-- **The arithmetic half of `deg [n] = n ^ 2`** (Silverman III.6.4(a) through
III.6.2(d)). The quotient `Φₙ/ΨSqₙ` is in lowest terms because `Φₙ` and
`ΨSqₙ` are coprime, so `RatFunc.finrank_eq_max_natDegree` reads the degree off
the numerator and denominator degrees `n ^ 2` and `≤ n ^ 2 - 1`.

The coprimality hypothesis is Tau Ceti's `isCoprime_Φ_ΨSq`; it is the exact
first field of this port and is not assumed unconditionally anywhere. -/
theorem finrank_adjoin_mulByIntX {n : ℤ} (hn : n ≠ 0)
    (hcop : IsCoprime (W.Φ n) (W.ΨSq n)) :
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
  rw [mulByIntX, RatFunc.finrank_eq_max_natDegree, RatFunc.num_div, RatFunc.denom_div _ hΨ]
  set g := gcd (W.Φ n) (W.ΨSq n)
  have hΨdiv : W.ΨSq n / g ≠ 0 := by
    rw [← hgcd, Polynomial.div_C]
    exact mul_ne_zero hΨ (Polynomial.C_ne_zero.mpr hcinv)
  have hlc : ((W.ΨSq n / g).leadingCoeff)⁻¹ ≠ 0 :=
    inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hΨdiv)
  have hΦnd : (Polynomial.C ((W.ΨSq n / g).leadingCoeff)⁻¹ * (W.Φ n / g)).natDegree =
      (W.Φ n).natDegree := by
    rw [Polynomial.natDegree_C_mul hlc, ← hgcd, Polynomial.div_C,
      Polynomial.natDegree_mul_C hcinv]
  have hΨnd : (Polynomial.C ((W.ΨSq n / g).leadingCoeff)⁻¹ * (W.ΨSq n / g)).natDegree =
      (W.ΨSq n).natDegree := by
    rw [Polynomial.natDegree_C_mul hlc, ← hgcd, Polynomial.div_C,
      Polynomial.natDegree_mul_C hcinv]
  rw [hΦnd, hΨnd, W.natDegree_Φ n]
  exact max_eq_left ((W.natDegree_ΨSq_le n).trans (Nat.sub_le _ _))

/-- **The middle tower degree**, `[F(W) : F(Φₙ/ΨSqₙ)] = 2 n ^ 2`, the
`finrank_ratFuncAdjoinΦDivΨSqRange` of Tau Ceti. -/
theorem finrank_mulByIntXRange_functionField {n : ℤ} (hn : n ≠ 0)
    (hcop : IsCoprime (W.Φ n) (W.ΨSq n)) :
    Module.finrank ((mulByIntXRange W n).extendRight W.toAffine.FunctionField)
      W.toAffine.FunctionField = 2 * n.natAbs ^ 2 := by
  rw [finrank_extendRight W (mulByIntXRange W n), mulByIntXRange,
    finrank_adjoin_mulByIntX W hn hcop]

/-- **`[F(W) : f(F(W'))] = n ^ 2`** for a function-field embedding whose pullback
of the affine coordinate is `Φₙ/ΨSqₙ`, in the finrank form of Tau Ceti's
`finrank_fieldRange_of_apply_X_eq_Φ_div_ΨSq`. -/
theorem finrank_fieldRange_of_apply_X_eq_mulByIntX {W' : WeierstrassCurve F} {n : ℤ}
    (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (hf : f (algebraMap F[X] W'.toAffine.FunctionField X) =
      algebraMap (RatFunc F) W.toAffine.FunctionField (mulByIntX W n))
    (hn : n ≠ 0) (hcop : IsCoprime (W.Φ n) (W.ΨSq n)) :
    Module.finrank f.fieldRange W.toAffine.FunctionField = n.natAbs ^ 2 := by
  rw [finrank_fieldRange_of_apply_X_eq W f hf, finrank_adjoin_mulByIntX W hn hcop]

/-! ## 4. The isogeny degree and its separable part -/

/-- **The degree of a function-field embedding**, in the sense of Tau Ceti's
`Isogeny.degree`: the dimension of the target function field over the image of
the pullback. -/
noncomputable def isogenyDegree {W₁ W₂ : WeierstrassCurve F}
    (f : W₁.toAffine.FunctionField →ₐ[F] W₂.toAffine.FunctionField) : ℕ :=
  Module.finrank f.fieldRange W₂.toAffine.FunctionField

/-- **The separable degree of a function-field embedding**, the separable degree
of the same extension. -/
noncomputable def isogenySeparableDegree {W₁ W₂ : WeierstrassCurve F}
    (f : W₁.toAffine.FunctionField →ₐ[F] W₂.toAffine.FunctionField) : ℕ :=
  Field.finSepDegree f.fieldRange W₂.toAffine.FunctionField

/-- **The inseparable degree of a function-field embedding.** -/
noncomputable def isogenyInseparableDegree {W₁ W₂ : WeierstrassCurve F}
    (f : W₁.toAffine.FunctionField →ₐ[F] W₂.toAffine.FunctionField) : ℕ :=
  Field.finInsepDegree f.fieldRange W₂.toAffine.FunctionField

/-- **The degree factors as separable times inseparable**, transported from the
field extension the isogeny degree measures. -/
theorem isogenySeparableDegree_mul_inseparableDegree {W₁ W₂ : WeierstrassCurve F}
    (f : W₁.toAffine.FunctionField →ₐ[F] W₂.toAffine.FunctionField) :
    isogenySeparableDegree f * isogenyInseparableDegree f = isogenyDegree f :=
  Field.finSepDegree_mul_finInsepDegree _ _

/-- **A separable isogeny has separable degree equal to its degree.** -/
theorem isogenySeparableDegree_eq_degree_of_isSeparable {W₁ W₂ : WeierstrassCurve F}
    (f : W₁.toAffine.FunctionField →ₐ[F] W₂.toAffine.FunctionField)
    [Algebra.IsSeparable f.fieldRange W₂.toAffine.FunctionField] :
    isogenySeparableDegree f = isogenyDegree f := by
  rw [isogenySeparableDegree, isogenyDegree,
    Field.finSepDegree_eq_finrank_of_isSeparable]

/-- **`deg [n] = n ^ 2`** (Silverman III.6.4(a)): a function-field embedding
whose pullback of the affine coordinate is `Φₙ/ΨSqₙ` has image of index exactly
`n ^ 2` in the target function field. -/
theorem degree_mulByIntIsogeny {W' : WeierstrassCurve F} {n : ℤ}
    (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (hf : f (algebraMap F[X] W'.toAffine.FunctionField X) =
      algebraMap (RatFunc F) W.toAffine.FunctionField (mulByIntX W n))
    (hn : n ≠ 0) (hcop : IsCoprime (W.Φ n) (W.ΨSq n)) :
    isogenyDegree f = n.natAbs ^ 2 :=
  finrank_fieldRange_of_apply_X_eq_mulByIntX W f hf hn hcop

/-- **A separable `[n]` has separable degree `n ^ 2`** (Silverman III.5.4 and
III.6.4(a)): in the separable case the separable degree is the whole degree,
which is `n ^ 2`.

The separability instance is the exact second field of this port: Tau Ceti
derives it from the invariant differential, which Mathlib v4.32.2 does not
provide. -/
theorem separableDegree_mulByIntIsogeny {W' : WeierstrassCurve F} {n : ℤ}
    (f : W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (hf : f (algebraMap F[X] W'.toAffine.FunctionField X) =
      algebraMap (RatFunc F) W.toAffine.FunctionField (mulByIntX W n))
    (hn : n ≠ 0) (hcop : IsCoprime (W.Φ n) (W.ΨSq n))
    [Algebra.IsSeparable f.fieldRange W.toAffine.FunctionField] :
    isogenySeparableDegree f = n.natAbs ^ 2 := by
  rw [isogenySeparableDegree_eq_degree_of_isSeparable,
    degree_mulByIntIsogeny W f hf hn hcop]

end WeierstrassCurve

/-! ## 5. Axiom footprint -/

#print axioms WeierstrassCurve.finrank_functionField
#print axioms WeierstrassCurve.finrank_adjoin_mulByIntX
#print axioms WeierstrassCurve.degree_mulByIntIsogeny
#print axioms WeierstrassCurve.separableDegree_mulByIntIsogeny
#print axioms WeierstrassCurve.isogenySeparableDegree_mul_inseparableDegree

end