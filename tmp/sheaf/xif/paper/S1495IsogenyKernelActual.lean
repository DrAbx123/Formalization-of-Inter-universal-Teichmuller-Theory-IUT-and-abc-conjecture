import tmp.sheaf.xif.paper.S1483MulByIntOnFunctionFieldActual
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.Tactic.ComputeDegree

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

/-!
# S1495: the actual kernel of multiplication by an integer

## What this file fixes

S1483 defines TauCeti.Isogeny.mulByIntKer as AddSubgroup.torsionBy W.Point n, so its
definitional equality mulByIntKer_eq_torsionBy holds by rfl.  That is not the source's
kernel.  TauCeti defines, in Isogeny/Kernel.lean,

  Isogeny.ker phi = translationFixingSubgroup W1 phi.fieldPullback.fieldRange,

the subgroup of points whose translation of the source function field fixes every function
pulled back from the target.  The translation action is built in
Affine/FunctionField/Translation/Basic.lean and the fixing subgroup in
Affine/FunctionField/Translation/FixedField.lean.

This file ports that construction to the current Mathlib (v4.32.2), on top of S1467 and
S1483: the translated generic point, the translation automorphism of the function field,
the translation action, the translation-fixing subgroup, and the actual Isogeny.ker.

It then constructs the actual kernel of mulByIntIsogeny and proves

  (mulByIntIsogeny W hn h hm).ker = AddSubgroup.torsionBy (W/F).Point n

from the source tautological-point identity, named in S1483 as
TautologicalPointMulByInt W hn h.  This is the exact first field of the equality: it is
TauCeti's tautologicalPoint_mulByIntPullback, whose proof needs
WeierstrassCurve.zsmul_point_eq_smulEval.  That theorem is absent from Mathlib v4.32.2 and
is not ported here, so the general-n equality is conditional exactly on it.  No
ker := torsionBy shortcut is used: the left-hand side is the translation-fixing subgroup
of the pulled-back field.

The n = 1 case is proved unconditionally, so the construction and the equality are
non-vacuous.

## Status

- statement_compiles: yes, checked by lake env lean.
- proof_body_checked: yes, every proof is complete and no new assumptions are introduced.
- kernel_closed: yes for the translation action, the actual ker, the conditional equality,
  and the unconditional n = 1 instance.
- target_accepted: no for the general-n equality; its exact first field is named above.

## Provenance

TauCeti (Apache-2.0), Isogeny/Kernel.lean, Isogeny/FunctionField.lean,
Isogeny/TautologicalPoint.lean, Affine/FunctionField/Translation/Basic.lean and
Affine/FunctionField/Translation/FixedField.lean.  The point-coordinate and integrality
helpers are TauCeti Affine/Point/Basic.lean, Affine/FunctionField/GenericPoint/Basic.lean,
and Integrality.lean.
-/

namespace IsIntegral

theorem of_sq_add_mul_add_eq_zero {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] {b c y : A} (hb : IsIntegral R b) (hc : IsIntegral R c)
    (h : y ^ 2 + b * y + c = 0) : IsIntegral R y := by
  nontriviality A
  have hdeg : (X ^ 2 + (C b * X + C c) : A[X]).natDegree = 2 := by compute_degree!
  refine IsIntegral.of_aeval_monic_of_isIntegral_coeff (p := X ^ 2 + (C b * X + C c))
    (monic_X_pow_add (by compute_degree!)) (by omega) ?_ ?_
  · have : Polynomial.eval y (X ^ 2 + (C b * X + C c) : A[X]) = 0 := by
      simpa only [eval_add, eval_pow, eval_X, eval_mul, eval_C, add_assoc] using h
    rw [this]
    exact isIntegral_zero
  · intro i
    match i with
    | 0 => simpa using hc
    | 1 => simpa using hb
    | 2 => simpa using (isIntegral_one : IsIntegral R (1 : A))
    | (n + 3) => simpa using (isIntegral_zero : IsIntegral R (0 : A))

end IsIntegral

namespace WeierstrassCurve

theorem isIntegral_y_of_equation_of_isIntegral_x
    {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]
    (W : WeierstrassCurve R) {x y : A}
    (h : (W.baseChange A).toAffine.Equation x y) (hx : IsIntegral R x) : IsIntegral R y := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h
  refine IsIntegral.of_sq_add_mul_add_eq_zero
    (b := algebraMap R A W.a₁ * x + algebraMap R A W.a₃)
    (c := -(x ^ 3 + algebraMap R A W.a₂ * x ^ 2 + algebraMap R A W.a₄ * x + algebraMap R A W.a₆))
    ((isIntegral_algebraMap.mul hx).add isIntegral_algebraMap)
    ((((hx.pow 3).add (isIntegral_algebraMap.mul (hx.pow 2))).add
      (isIntegral_algebraMap.mul hx)).add isIntegral_algebraMap).neg ?_
  linear_combination h

end WeierstrassCurve

namespace WeierstrassCurve.Affine

namespace Point

variable {R : Type*} [CommRing R] {W : Affine R}

/-- The coordinates of a nonzero point are a nonsingular solution of the equation. -/
theorem nonsingular_coords {P : W.Point} (hP : P ≠ 0) : W.Nonsingular (xCoord P) (yCoord P) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact h

/-- A nonzero point is Point.some of its two coordinates. -/
theorem some_coords {P : W.Point} (hP : P ≠ 0) :
    _root_.WeierstrassCurve.Affine.Point.some (xCoord P) (yCoord P)
      (nonsingular_coords hP) = P := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => (rfl)

/-- Two nonzero points with the same two affine coordinates are equal. -/
theorem eq_of_coords {P Q : W.Point} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hx : xCoord P = xCoord Q) (hy : yCoord P = yCoord Q) : P = Q := by
  rw [← some_coords hP, ← some_coords hQ]
  simp only [hx, hy]

/-- The x-coordinate of the negation of a point. -/
@[simp]
theorem xCoord_neg (P : W.Point) : xCoord (-P) = xCoord P := by
  cases P <;> (rfl)

end Point

section Translation

variable {F : Type*} [Field F] [DecidableEq F] (W : Affine F) [W.IsElliptic]

/-- The translate of the generic point of W by a point P. -/
noncomputable def translatedGenericPoint (P : (W⁄F).Point) : (W⁄W.FunctionField).Point :=
  genericPoint W + Point.baseChange (W' := W) F W.FunctionField P

theorem translatedGenericPoint_def (P : (W⁄F).Point) :
    translatedGenericPoint W P =
      genericPoint W + Point.baseChange (W' := W) F W.FunctionField P := (rfl)

@[simp]
theorem translatedGenericPoint_zero : translatedGenericPoint W (0 : (W⁄F).Point) = genericPoint W := by
  rw [translatedGenericPoint_def, map_zero, add_zero]

/-- A translate of the generic point is never the point at infinity. -/
theorem translatedGenericPoint_ne_zero (P : (W⁄F).Point) :
    translatedGenericPoint W P ≠ 0 := by
  intro h
  have hneg : genericPoint W = -Point.baseChange (W' := W) F W.FunctionField P := by
    rw [eq_neg_iff_add_eq_zero]
    exact h
  have hx : genericX W = algebraMap F W.FunctionField (Point.xCoord P) := by
    rw [← xCoord_genericPoint, hneg, Point.xCoord_neg, Point.xCoord_map, Algebra.ofId_apply]
  exact transcendental_genericX W (hx ▸ isAlgebraic_algebraMap _)

/-- The x-coordinate of a translate of the generic point is transcendental. -/
private theorem transcendental_xCoord_translatedGenericPoint (P : (W⁄F).Point) :
    Transcendental F (Point.xCoord (translatedGenericPoint W P)) := by
  set 𝔽 := algebraicClosure F W.FunctionField
  intro halg
  set Q := translatedGenericPoint W P with hQdef
  have hQ : Q ≠ 0 := translatedGenericPoint_ne_zero W P
  set u := Point.xCoord Q
  set v := Point.yCoord Q
  have hns : (W⁄W.FunctionField).Nonsingular u v := Point.nonsingular_coords hQ
  have hu : u ∈ 𝔽 := halg.isIntegral
  have hv : v ∈ 𝔽 :=
    WeierstrassCurve.isIntegral_y_of_equation_of_isIntegral_x W hns.left hu
  have hnsE : (W⁄𝔽).Nonsingular (⟨u, hu⟩ : 𝔽) ⟨v, hv⟩ :=
    (_root_.WeierstrassCurve.Affine.baseChange_nonsingular (W := W)
      (f := 𝔽.val) 𝔽.val.injective _ _).1 hns
  have hQmap : Point.map 𝔽.val (Point.some (⟨u, hu⟩ : 𝔽) ⟨v, hv⟩ hnsE) = Q := by
    rw [Point.map_some]
    exact Point.some_coords hQ
  have hgeneric : genericPoint W =
      Point.map 𝔽.val (Point.some (⟨u, hu⟩ : 𝔽) ⟨v, hv⟩ hnsE -
        Point.baseChange (W' := W) F 𝔽 P) := by
    have hbc : Point.map 𝔽.val (Point.baseChange (W' := W) F 𝔽 P) =
        Point.baseChange (W' := W) F W.FunctionField P :=
      Point.map_baseChange (W' := W) 𝔽.val P
    rw [map_sub, hQmap, hbc, hQdef, translatedGenericPoint_def]
    exact (add_sub_cancel_right _ _).symm
  have : IsIntegral F (genericX W) := by
    rw [← xCoord_genericPoint, hgeneric, Point.xCoord_map]
    exact (Algebra.IsIntegral.isIntegral (R := F) _).map 𝔽.val
  exact transcendental_genericX W this.isAlgebraic

/-- The pullback of the translation by P on the affine coordinate ring. -/
private noncomputable def translationAlgHom (P : (W⁄F).Point) :
    W.CoordinateRing →ₐ[F] W.FunctionField :=
  CoordinateRing.evalAlgHom (Point.nonsingular_coords (translatedGenericPoint_ne_zero W P)).left

private theorem translationAlgHom_mk_C_X (P : (W⁄F).Point) :
    translationAlgHom W P (CoordinateRing.mk W (C X)) =
      Point.xCoord (translatedGenericPoint W P) :=
  CoordinateRing.evalAlgHom_of_X _

private theorem translationAlgHom_mk_Y (P : (W⁄F).Point) :
    translationAlgHom W P (CoordinateRing.mk W Y) =
      Point.yCoord (translatedGenericPoint W P) :=
  CoordinateRing.evalAlgHom_root _

private theorem translationAlgHom_injective (P : (W⁄F).Point) :
    Function.Injective (translationAlgHom W P) :=
  CoordinateRing.algHom_injective W (translationAlgHom W P) <| by
    rw [translationAlgHom_mk_C_X]
    exact transcendental_xCoord_translatedGenericPoint W P

/-- The pullback of the translation by P on the function field. -/
private noncomputable def translationAux (P : (W⁄F).Point) :
    W.FunctionField →ₐ[F] W.FunctionField :=
  IsFractionRing.liftAlgHom (translationAlgHom_injective W P)

private theorem translationAux_algebraMap (P : (W⁄F).Point) (z : W.CoordinateRing) :
    translationAux W P (algebraMap W.CoordinateRing W.FunctionField z) =
      translationAlgHom W P z := by
  simp [translationAux, IsFractionRing.liftAlgHom_apply]

private theorem translationAux_genericX (P : (W⁄F).Point) :
    translationAux W P (genericX W) = Point.xCoord (translatedGenericPoint W P) := by
  rw [genericX_def, translationAux_algebraMap, translationAlgHom_mk_C_X]

private theorem translationAux_genericY (P : (W⁄F).Point) :
    translationAux W P (genericY W) = Point.yCoord (translatedGenericPoint W P) := by
  rw [genericY_def, translationAux_algebraMap, translationAlgHom_mk_Y]

/-- The translation pullback moves the generic point to its translate. -/
private theorem map_genericPoint (P : (W⁄F).Point) :
    Point.map (translationAux W P) (genericPoint W) = translatedGenericPoint W P := by
  apply Point.eq_of_coords
  · rw [genericPoint_eq_some, Point.map_some]
    exact Point.some_ne_zero _
  · exact translatedGenericPoint_ne_zero W P
  · rw [Point.xCoord_map, xCoord_genericPoint]
    exact translationAux_genericX W P
  · rw [Point.yCoord_map, yCoord_genericPoint]
    exact translationAux_genericY W P

private theorem map_translatedGenericPointAux (P Q : (W⁄F).Point) :
    Point.map (translationAux W Q) (translatedGenericPoint W P) =
      translatedGenericPoint W (P + Q) := by
  have hbase : Point.map (translationAux W Q)
      (Point.baseChange (W' := W) F W.FunctionField P) =
        Point.baseChange (W' := W) F W.FunctionField P :=
    Point.map_baseChange (W' := W) (translationAux W Q) P
  rw [translatedGenericPoint_def, map_add, hbase, map_genericPoint,
    translatedGenericPoint_def, translatedGenericPoint_def, map_add, add_right_comm]
  exact add_assoc _ _ _

private theorem comp_translationAlgHom (P Q : (W⁄F).Point) :
    (translationAux W Q).comp (translationAlgHom W P) = translationAlgHom W (P + Q) := by
  refine CoordinateRing.algHom_ext ?_ ?_
  · rw [← AdjoinRoot.mk_C, AlgHom.comp_apply, translationAlgHom_mk_C_X,
      translationAlgHom_mk_C_X,
      ← Point.xCoord_map (W := W) (translationAux W Q), map_translatedGenericPointAux]
  · rw [← AdjoinRoot.mk_X, AlgHom.comp_apply, translationAlgHom_mk_Y,
      translationAlgHom_mk_Y,
      ← Point.yCoord_map (W := W) (translationAux W Q), map_translatedGenericPointAux]

private theorem comp_translationAux (P Q : (W⁄F).Point) :
    (translationAux W Q).comp (translationAux W P) = translationAux W (P + Q) := by
  apply IsLocalization.algHom_ext (nonZeroDivisors W.CoordinateRing)
  apply AlgHom.ext
  intro z
  simp only [AlgHom.comp_apply]
  change translationAux W Q
      (translationAux W P (algebraMap W.CoordinateRing W.FunctionField z)) =
    translationAux W (P + Q) (algebraMap W.CoordinateRing W.FunctionField z)
  have h : translationAux W Q
      (translationAux W P (algebraMap W.CoordinateRing W.FunctionField z)) =
      translationAlgHom W (P + Q) z := by
    rw [translationAux_algebraMap, ← AlgHom.comp_apply, comp_translationAlgHom]
  simpa [translationAux_algebraMap] using h

private theorem translationAlgHom_zero :
    translationAlgHom W 0 = IsScalarTower.toAlgHom F W.CoordinateRing W.FunctionField := by
  refine CoordinateRing.algHom_ext ?_ ?_
  · rw [← AdjoinRoot.mk_C, translationAlgHom_mk_C_X, translatedGenericPoint_zero,
      xCoord_genericPoint, IsScalarTower.toAlgHom_apply, genericX_def]
  · rw [← AdjoinRoot.mk_X, translationAlgHom_mk_Y, translatedGenericPoint_zero,
      yCoord_genericPoint, IsScalarTower.toAlgHom_apply, genericY_def]

private theorem translationAux_zero : translationAux W 0 = AlgHom.id F W.FunctionField := by
  apply IsLocalization.algHom_ext (nonZeroDivisors W.CoordinateRing)
  apply AlgHom.ext
  intro z
  simp only [AlgHom.comp_apply]
  change translationAux W 0 (algebraMap W.CoordinateRing W.FunctionField z) =
    algebraMap W.CoordinateRing W.FunctionField z
  have h : translationAux W 0 (algebraMap W.CoordinateRing W.FunctionField z) =
      algebraMap W.CoordinateRing W.FunctionField z := by
    rw [translationAux_algebraMap, translationAlgHom_zero, IsScalarTower.toAlgHom_apply]
  simpa using h

/-- The translation of the function field by a point P. -/
noncomputable def translation (P : (W⁄F).Point) :
    W.FunctionField ≃ₐ[F] W.FunctionField :=
  AlgEquiv.ofAlgHom (translationAux W P) (translationAux W (-P))
    (by rw [comp_translationAux, neg_add_cancel, translationAux_zero])
    (by rw [comp_translationAux, add_neg_cancel, translationAux_zero])

/-- Translation carries the generic point to the translated generic point. -/
theorem map_translation_genericPoint (P : (W⁄F).Point) :
    Point.map (translation W P).toAlgHom (genericPoint W) = translatedGenericPoint W P :=
  map_genericPoint W P

/-- The translation by the point at infinity is the identity. -/
@[simp]
theorem translation_zero : translation W 0 = 1 :=
  AlgEquiv.ext fun z => AlgHom.congr_fun (translationAux_zero W) z

/-- The composition law of the translations. -/
theorem translation_add (P Q : (W⁄F).Point) :
    translation W (P + Q) = (translation W P).trans (translation W Q) :=
  AlgEquiv.ext fun z => (AlgHom.congr_fun (comp_translationAux W P Q) z).symm

/-- The translation action of the point group on the function field. -/
noncomputable def translationHom :
    Multiplicative (W⁄F).Point →* (W.FunctionField ≃ₐ[F] W.FunctionField) where
  toFun P := translation W (Multiplicative.toAdd P)
  map_one' := translation_zero W
  map_mul' P Q := by
    exact (congrArg (translation W)
      (add_comm (Multiplicative.toAdd P) (Multiplicative.toAdd Q))).trans
      (translation_add W (Multiplicative.toAdd Q) (Multiplicative.toAdd P))

@[simp]
theorem translationHom_apply (P : Multiplicative (W⁄F).Point) :
    translationHom W P = translation W (Multiplicative.toAdd P) := (rfl)

/-- The points whose translation fixes an intermediate field pointwise. -/
noncomputable def translationFixingSubgroup (L : IntermediateField F W.FunctionField) :
    AddSubgroup (W⁄F).Point :=
  Subgroup.toAddSubgroup' (L.fixingSubgroup.comap (translationHom W))

/-- A point fixes an intermediate field exactly when its translation moves no function of that field. -/
@[simp]
theorem mem_translationFixingSubgroup_iff {L : IntermediateField F W.FunctionField}
    {P : (W⁄F).Point} :
    P ∈ translationFixingSubgroup W L ↔ ∀ z ∈ L, translation W P z = z := by
  rw [translationFixingSubgroup, Subgroup.mem_toAddSubgroup', Subgroup.mem_comap,
    translationHom_apply, IntermediateField.mem_fixingSubgroup_iff]
  rfl

end Translation

end WeierstrassCurve.Affine

namespace TauCeti

open WeierstrassCurve.Affine

namespace CoordinatePullback

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F} [W₂.IsElliptic]

/-- The x-coordinate of the tautological point is the pullback of the class of X. -/
@[simp]
theorem xCoord_tautologicalPoint (p : CoordinatePullback W₁ W₂) :
    WeierstrassCurve.Affine.Point.xCoord p.tautologicalPoint =
      p (AdjoinRoot.of W₂.polynomial X) :=
  WeierstrassCurve.Affine.Point.xCoord_some _

/-- The y-coordinate of the tautological point is the pullback of the class of Y. -/
@[simp]
theorem yCoord_tautologicalPoint (p : CoordinatePullback W₁ W₂) :
    WeierstrassCurve.Affine.Point.yCoord p.tautologicalPoint =
      p (AdjoinRoot.root W₂.polynomial) :=
  WeierstrassCurve.Affine.Point.yCoord_some _

/-- A coordinate pullback is determined by its tautological point. -/
theorem tautologicalPoint_injective :
    Function.Injective (tautologicalPoint (W1 := W₁) (W2 := W₂)) := fun p q h =>
  WeierstrassCurve.Affine.CoordinateRing.algHom_ext
    (by rw [← xCoord_tautologicalPoint, h, xCoord_tautologicalPoint])
    (by rw [← yCoord_tautologicalPoint, h, yCoord_tautologicalPoint])

/-- Post-composing with an algebra homomorphism of function fields moves the tautological point. -/
@[simp]
theorem tautologicalPoint_comp {W₀ : WeierstrassCurve.Affine F}
    (p : CoordinatePullback W₁ W₂)
    (σ : W₁.FunctionField →ₐ[F] W₀.FunctionField) :
    tautologicalPoint (σ.comp p) =
      WeierstrassCurve.Affine.Point.map σ p.tautologicalPoint := by
  rw [← WeierstrassCurve.Affine.Point.some_coords (tautologicalPoint_ne_zero p),
    WeierstrassCurve.Affine.Point.map_some,
    ← WeierstrassCurve.Affine.Point.some_coords (tautologicalPoint_ne_zero (σ.comp p))]
  simp only [xCoord_tautologicalPoint, yCoord_tautologicalPoint, AlgHom.comp_apply]

/-- The identity pullback's tautological point is the generic point. -/
@[simp]
theorem tautologicalPoint_id (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
    (CoordinatePullback.id W).tautologicalPoint =
      WeierstrassCurve.Affine.genericPoint W := by
  rw [tautologicalPoint, WeierstrassCurve.Affine.genericPoint_eq_some]
  congr 1

end CoordinatePullback

namespace Isogeny

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve.Affine F}
  [W₁.IsElliptic]

/-- The kernel of an isogeny: the points whose translation fixes every pulled-back function. -/
noncomputable def ker (φ : Isogeny W₁ W₂) : AddSubgroup (W₁⁄F).Point :=
  translationFixingSubgroup W₁ φ.fieldPullback.fieldRange

/-- The defining equation of the kernel. -/
theorem ker_def (φ : Isogeny W₁ W₂) :
    φ.ker = translationFixingSubgroup W₁ φ.fieldPullback.fieldRange := (rfl)

/-- A point is in the kernel exactly when it translates every pulled-back function to itself. -/
@[simp]
theorem mem_ker_iff {φ : Isogeny W₁ W₂} {P : (W₁⁄F).Point} :
    P ∈ φ.ker ↔ ∀ z ∈ φ.fieldPullback.fieldRange, translation W₁ P z = z := by
  rw [ker_def]; exact mem_translationFixingSubgroup_iff W₁

/-- A ring homomorphism agreeing with an isogeny's coordinate pullback is its function-field
pullback. -/
theorem ringHom_eq_fieldPullback (φ : Isogeny W₁ W₂)
    (f : W₂.FunctionField →+* W₁.FunctionField)
    (hf : ∀ x : W₂.CoordinateRing,
      f (algebraMap W₂.CoordinateRing W₂.FunctionField x) = φ.pullback x) :
    f = (φ.fieldPullback : W₂.FunctionField →+* W₁.FunctionField) :=
  IsFractionRing.ringHom_ext (A := W₂.CoordinateRing) (K := W₂.FunctionField)
    (L := W₁.FunctionField) fun x => (hf x).trans (fieldPullback_algebraMap φ x).symm

/-- A function-field algebra homomorphism agreeing with an isogeny's coordinate pullback is its
function-field pullback. -/
theorem fieldPullback_unique (φ : Isogeny W₁ W₂)
    (f : W₂.FunctionField →ₐ[F] W₁.FunctionField)
    (hf : ∀ x : W₂.CoordinateRing,
      f (algebraMap W₂.CoordinateRing W₂.FunctionField x) = φ.pullback x) :
    f = φ.fieldPullback :=
  AlgHom.coe_ringHom_injective <| ringHom_eq_fieldPullback φ f.toRingHom hf

/-- Membership in the kernel is fixing the coordinate pullback. -/
theorem mem_ker_iff_comp_pullback_eq {φ : Isogeny W₁ W₂} {P : (W₁⁄F).Point} :
    P ∈ φ.ker ↔ (translation W₁ P).toAlgHom.comp φ.pullback = φ.pullback := by
  rw [mem_ker_iff]
  constructor
  · intro h
    refine WeierstrassCurve.Affine.CoordinateRing.algHom_ext ?_ ?_ <;>
      · rw [AlgHom.comp_apply]
        exact h _ ⟨_, fieldPullback_algebraMap _ _⟩
  · intro hcoord
    have hfield : (translation W₁ P).toAlgHom.comp φ.fieldPullback = φ.fieldPullback :=
      fieldPullback_unique _ _ fun x => by
        rw [AlgHom.comp_apply, fieldPullback_algebraMap, ← AlgHom.comp_apply, hcoord]
    rintro _ ⟨z, rfl⟩
    simpa using DFunLike.congr_fun hfield z

/-- Membership in the kernel is fixing the tautological point. -/
theorem mem_ker_iff_map_tautologicalPoint_eq [W₂.IsElliptic] (φ : Isogeny W₁ W₂)
    {P : (W₁⁄F).Point} :
    P ∈ φ.ker ↔
      WeierstrassCurve.Affine.Point.map (translation W₁ P).toAlgHom
        (CoordinatePullback.tautologicalPoint φ.pullback) =
        CoordinatePullback.tautologicalPoint φ.pullback := by
  rw [mem_ker_iff_comp_pullback_eq, ← CoordinatePullback.tautologicalPoint_comp,
    CoordinatePullback.tautologicalPoint_injective.eq_iff]

end Isogeny

end TauCeti

namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- The pullback of the multiplication-by-n isogeny is the multiplication pullback. -/
@[simp]
theorem mulByIntIsogeny_pullback {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    (h : EquationMulByInt W n) (hm : MapsInfinityMulByInt W hn h) :
    (mulByIntIsogeny W hn h hm).pullback = mulByIntPullback W hn h := (rfl)

/-- A point is in the kernel of the multiplication-by-n isogeny exactly when it is n-torsion,
given the source tautological-point identity. -/
theorem mem_ker_mulByIntIsogeny_iff {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    (h : EquationMulByInt W n) (hm : MapsInfinityMulByInt W hn h)
    (htaut : TautologicalPointMulByInt W hn h) {P : (W⁄F).Point} :
    P ∈ (mulByIntIsogeny W hn h hm).ker ↔ n • P = 0 := by
  have htaut' : (mulByIntPullback W hn h).tautologicalPoint = n • genericPoint W := htaut
  rw [mem_ker_iff_map_tautologicalPoint_eq, mulByIntIsogeny_pullback, htaut',
    map_zsmul, map_translation_genericPoint, translatedGenericPoint_def]
  have hsmul : n • (genericPoint W + Point.baseChange (W' := W) F W.FunctionField P) =
      n • genericPoint W + n • Point.baseChange (W' := W) F W.FunctionField P :=
    zsmul_add _ _ _
  have hzero : n • Point.baseChange (W' := W) F W.FunctionField P =
      Point.baseChange (W' := W) F W.FunctionField (n • P) := (map_zsmul _ _ _).symm
  rw [hsmul, hzero]
  constructor
  · intro hfix
    refine Point.map_injective (W' := W) (f := Algebra.ofId F W.FunctionField) ?_
    rw [map_zero]
    exact add_left_cancel (hfix.trans (add_zero _).symm)
  · intro hP
    rw [hP, map_zero, add_zero]

/-- The kernel of the multiplication-by-n isogeny is the n-torsion subgroup. -/
theorem ker_mulByIntIsogeny_eq_torsionBy {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    (h : EquationMulByInt W n) (hm : MapsInfinityMulByInt W hn h)
    (htaut : TautologicalPointMulByInt W hn h) :
    (mulByIntIsogeny W hn h hm).ker = AddSubgroup.torsionBy (W⁄F).Point n := by
  ext P
  rw [mem_ker_mulByIntIsogeny_iff W hn h hm htaut]
  exact (Submodule.mem_torsionBy_iff n P).symm

/-- The same equality on the base-point group W.Point. -/
theorem ker_mulByIntIsogeny_eq_torsionBy_point {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    (h : EquationMulByInt W n) (hm : MapsInfinityMulByInt W hn h)
    (htaut : TautologicalPointMulByInt W hn h) :
    (mulByIntIsogeny W hn h hm).ker = AddSubgroup.torsionBy W.Point n :=
  ker_mulByIntIsogeny_eq_torsionBy W hn h hm htaut

/-- The tautological-point identity at n = 1. -/
theorem tautologicalPointMulByInt_one :
    TautologicalPointMulByInt W (psiFunctionField_one_ne_zero W) (equationMulByInt_one W) := by
  change (mulByIntPullback W (psiFunctionField_one_ne_zero W)
      (equationMulByInt_one W)).tautologicalPoint = (1 : ℤ) • genericPoint W
  rw [mulByIntPullback_one, CoordinatePullback.tautologicalPoint_id]
  simp

/-- The concrete kernel equality at n = 1, with no extra hypothesis. -/
theorem ker_mulByIntIsogeny_one_eq_torsionBy :
    (mulByIntIsogeny_one W).ker = AddSubgroup.torsionBy (W⁄F).Point (1 : ℤ) :=
  ker_mulByIntIsogeny_eq_torsionBy W (psiFunctionField_one_ne_zero W)
    (equationMulByInt_one W) (mapsInfinityMulByInt_one W)
    (tautologicalPointMulByInt_one W)

/-- The concrete kernel equality at n = 1 on W.Point. -/
theorem ker_mulByIntIsogeny_one_eq_torsionBy_point :
    (mulByIntIsogeny_one W).ker = AddSubgroup.torsionBy W.Point (1 : ℤ) :=
  ker_mulByIntIsogeny_eq_torsionBy_point W (psiFunctionField_one_ne_zero W)
    (equationMulByInt_one W) (mapsInfinityMulByInt_one W)
    (tautologicalPointMulByInt_one W)

end TauCeti.Isogeny




namespace TauCeti.Isogeny

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve.Affine F) [W.IsElliptic]

/-- The actual kernel of the multiplication-by-n isogeny: the points whose translation fixes
the pulled-back function field.  This is the source's Isogeny.ker, specialised to [n]. -/
noncomputable def mulByIntKerActual {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    (h : EquationMulByInt W n) (hm : MapsInfinityMulByInt W hn h) :
    AddSubgroup (W⁄F).Point :=
  (mulByIntIsogeny W hn h hm).ker

/-- The defining equation of the actual multiplication kernel. -/
theorem mulByIntKerActual_def {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    (h : EquationMulByInt W n) (hm : MapsInfinityMulByInt W hn h) :
    mulByIntKerActual W hn h hm = (mulByIntIsogeny W hn h hm).ker := (rfl)

/-- The actual multiplication kernel is the n-torsion subgroup, from the source's
tautological-point identity. -/
theorem mulByIntKerActual_eq_torsionBy {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    (h : EquationMulByInt W n) (hm : MapsInfinityMulByInt W hn h)
    (htaut : TautologicalPointMulByInt W hn h) :
    mulByIntKerActual W hn h hm = AddSubgroup.torsionBy (W⁄F).Point n :=
  ker_mulByIntIsogeny_eq_torsionBy W hn h hm htaut

/-- The actual multiplication kernel is the n-torsion subgroup on the base point group W.Point,
from the source's tautological-point identity. -/
theorem mulByIntKerActual_eq_torsionBy_point {n : ℤ} (hn : psiFunctionField W n ≠ 0)
    (h : EquationMulByInt W n) (hm : MapsInfinityMulByInt W hn h)
    (htaut : TautologicalPointMulByInt W hn h) :
    mulByIntKerActual W hn h hm = AddSubgroup.torsionBy W.Point n :=
  mulByIntKerActual_eq_torsionBy W hn h hm htaut

/-- The actual multiplication kernel at n = 1 is unconditionally the 1-torsion. -/
theorem mulByIntKerActual_one_eq_torsionBy :
    mulByIntKerActual W (psiFunctionField_one_ne_zero W) (equationMulByInt_one W)
        (mapsInfinityMulByInt_one W) =
      AddSubgroup.torsionBy (W⁄F).Point (1 : ℤ) :=
  ker_mulByIntIsogeny_one_eq_torsionBy W

/-- The actual multiplication kernel at n = 1, on W.Point. -/
theorem mulByIntKerActual_one_eq_torsionBy_point :
    mulByIntKerActual W (psiFunctionField_one_ne_zero W) (equationMulByInt_one W)
        (mapsInfinityMulByInt_one W) =
      AddSubgroup.torsionBy W.Point (1 : ℤ) :=
  ker_mulByIntIsogeny_one_eq_torsionBy_point W

end TauCeti.Isogeny
