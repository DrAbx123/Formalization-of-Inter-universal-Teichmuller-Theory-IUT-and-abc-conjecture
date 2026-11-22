import LeanFormal.IUT.Foundations.Geometry.TateCoordinateNormalization
import LeanFormal.IUT.Foundations.Geometry.TateUniformizationPointMap
import LeanFormal.IUT.Foundations.Geometry.WeierstrassVariableChangePoints

open WeierstrassCurve

set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.TateCurve.TateGroupLaw

noncomputable section

universe u

variable {K : Type u} [NormedField K] [CompleteSpace K] [CharZero K] [DecidableEq K]

/-- The Weierstrass variable change carrying normalized Tate coordinates back to the
raw coordinate pair: `(X, Y) ↦ (X + 2s, Y + s)` with `s = tateCoordinateCorrection q`. -/
noncomputable def tateNormalizationVariableChange (q : K) : VariableChange K where
  u := 1
  r := 2 * tateCoordinateCorrection q
  s := 0
  t := -tateCoordinateCorrection q

lemma tateNormalizationChangeX (q u : K) :
    weierstrassChangeX (tateNormalizationVariableChange (K := K) q)
        (normalizedTateX q u) = tateWeierstrassX q u := by
  dsimp [weierstrassChangeX, tateNormalizationVariableChange, normalizedTateX]
  ring

lemma tateNormalizationChangeY (q u : K) :
    weierstrassChangeY (tateNormalizationVariableChange (K := K) q)
        (normalizedTateX q u) (normalizedTateY q u) = tateWeierstrassY q u := by
  dsimp [weierstrassChangeY, tateNormalizationVariableChange, normalizedTateX,
    normalizedTateY]
  ring

/-- The Weierstrass curve whose coordinates are the raw Tate series pair. -/
noncomputable def tateNormalizationCurve (q : K) : WeierstrassCurve K :=
  tateNormalizationVariableChange (K := K) q • weierstrassCurve K q

/-- The coordinate change is an actual additive equivalence of point groups, so the
raw and normalized Tate point laws are compatible with Mathlib's Weierstrass group law. -/
noncomputable def tateNormalizationPointEquiv (q : K) [hW : (weierstrassCurve K q).IsElliptic] :
    (tateNormalizationCurve (K := K) q).toAffine.Point ≃+
      (weierstrassCurve K q).toAffine.Point :=
  weierstrassVariableChangePointEquiv (weierstrassCurve K q)
    (tateNormalizationVariableChange (K := K) q)

@[simp] theorem tateNormalizationPointEquiv_apply (q : K) [hW : (weierstrassCurve K q).IsElliptic]
    (P : (tateNormalizationCurve (K := K) q).toAffine.Point) :
    tateNormalizationPointEquiv q P =
      weierstrassVariableChangePointMap (weierstrassCurve K q)
        (tateNormalizationVariableChange (K := K) q) P := rfl

theorem tateNormalizationPointEquiv_add (q : K) [hW : (weierstrassCurve K q).IsElliptic]
    (P Q : (tateNormalizationCurve (K := K) q).toAffine.Point) :
    tateNormalizationPointEquiv q (P + Q) =
      tateNormalizationPointEquiv q P + tateNormalizationPointEquiv q Q :=
  map_add (tateNormalizationPointEquiv q) P Q


/-! ## Conditional point bijection and group-law transport

The analytic point bijection is not assumed to be an additive map; it is only the
actual bijection `TateUniformizationPointMapGap` (injectivity and surjectivity onto
the nonzero affine points).  Extending it by `none ↦ 0` gives a bijection between the
one-point completion of the parameter quotient and the full Weierstrass point group;
the group law on the completion is then transported from the curve along that
bijection, and the coordinate-change `AddEquiv` is compatible with it.
-/

abbrev TatePointCompletion (q : K) (hq0 : q ≠ 0) : Type u :=
  Option (TateParameterQuotient q hq0)

noncomputable def tatePointBijection (q : K) (hq0 : q ≠ 0)
    (hdata : TateWeierstrassPointData q)
    (hgap : TateUniformizationPointMapGap q hq0 hdata) :
    TatePointCompletion q hq0 ≃ (weierstrassCurve K q).toAffine.Point where
  toFun := fun o => o.elim 0 (fun w => tateQuotientPoint q hq0 hdata w)
  invFun := fun P => if hP : P = 0 then none else
    some (Classical.choose (hgap.2 P hP))
  left_inv := by
    intro o
    cases o with
    | none => simp
    | some w =>
      have hne : tateQuotientPoint q hq0 hdata w ≠ 0 :=
        tateQuotientPoint_ne_zero hq0 hdata w
      simp only [Option.elim_some, dif_neg hne]
      have hspec := Classical.choose_spec (hgap.2 (tateQuotientPoint q hq0 hdata w) hne)
      exact congrArg some (hgap.1 hspec)
  right_inv := by
    intro P
    by_cases hP : P = 0
    · subst P
      simp
    · simp only [dif_neg hP]
      simp only [Option.elim_some]
      exact Classical.choose_spec (hgap.2 P hP)

/-- Conditional group law on the completed parameter quotient: addition is defined by
transporting the Weierstrass group law along the actual point bijection. -/
noncomputable def tateCompletionAdd {q : K} (hq0 : q ≠ 0)
    (e : TatePointCompletion (K := K) q hq0 ≃
      (weierstrassCurve K q).toAffine.Point) :
    TatePointCompletion (K := K) q hq0 →
      TatePointCompletion (K := K) q hq0 → TatePointCompletion (K := K) q hq0 :=
  fun x y => e.symm (e x + e y)

theorem tateCompletionAdd_eq_transport {q : K} (hq0 : q ≠ 0)
    (e : TatePointCompletion (K := K) q hq0 ≃
      (weierstrassCurve K q).toAffine.Point)
    (x y : TatePointCompletion (K := K) q hq0) :
    e (tateCompletionAdd hq0 e x y) = e x + e y := by
  unfold tateCompletionAdd
  exact Equiv.apply_symm_apply e (e x + e y)
/-- The conditional group operation attached to the actual point bijection. -/
noncomputable def tatePointGroupLaw (q : K) (hq0 : q ≠ 0)
    (hdata : TateWeierstrassPointData q)
    (hgap : TateUniformizationPointMapGap q hq0 hdata) :
    TatePointCompletion (K := K) q hq0 →
      TatePointCompletion (K := K) q hq0 → TatePointCompletion (K := K) q hq0 :=
  tateCompletionAdd hq0 (tatePointBijection (K := K) q hq0 hdata hgap)

theorem tatePointBijection_add (q : K) (hq0 : q ≠ 0)
    (hdata : TateWeierstrassPointData q)
    (hgap : TateUniformizationPointMapGap q hq0 hdata)
    (x y : TatePointCompletion (K := K) q hq0) :
    tatePointBijection (K := K) q hq0 hdata hgap (tatePointGroupLaw q hq0 hdata hgap x y) =
      tatePointBijection (K := K) q hq0 hdata hgap x +
        tatePointBijection (K := K) q hq0 hdata hgap y :=
  tateCompletionAdd_eq_transport hq0 (tatePointBijection (K := K) q hq0 hdata hgap) x y
theorem tateNormalizationPointEquiv_compat (q : K) [hW : (weierstrassCurve K q).IsElliptic]
    (P : (tateNormalizationCurve (K := K) q).toAffine.Point) :
    tateNormalizationPointEquiv q P =
      weierstrassVariableChangePointMap (weierstrassCurve K q)
        (tateNormalizationVariableChange (K := K) q) P := rfl

end
end LeanFormal.IUT.TateCurve.TateGroupLaw