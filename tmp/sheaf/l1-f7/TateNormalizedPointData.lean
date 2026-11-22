import LeanFormal.IUT.Foundations.Geometry.TateCoordinateNormalization
import LeanFormal.IUT.Foundations.Geometry.TateUniformizationPointMap

namespace LeanFormal.IUT.TateCurve

noncomputable section

universe u

variable {K : Type u} [NormedField K] [CharZero K]

/-- Canonical normalized-coordinate point data: the normalized pair is
nonsingular on the canonical q-curve for every legal parameter. -/
def TateNormalizedPointData (q : K) : Prop :=
  ∀ u : ↥(coordinateParameterDomain q),
    (weierstrassCurve K q).toAffine.Nonsingular
      (normalizedTateX q (u : K)) (normalizedTateY q (u : K))

/-- The canonical point map on the quotient of K^x by q^Z, using the
normalized Tate coordinates. -/
noncomputable def normalizedTateQuotientPoint (q : K)
    (parameterNeZero : q ≠ 0) (hdata : TateNormalizedPointData q) :
    TateParameterQuotient q parameterNeZero → (weierstrassCurve K q).toAffine.Point :=
  Quotient.lift
    (fun u => WeierstrassCurve.Affine.Point.some
      (normalizedTateX q (u : K)) (normalizedTateY q (u : K)) (hdata u))
    (by
      intro u v huv
      obtain ⟨m, hm⟩ := huv
      rw [WeierstrassCurve.Affine.Point.some.injEq]
      constructor
      · rw [← hm, normalizedTateX_zpow_mul_parameter parameterNeZero m (u : K)]
      · rw [← hm, normalizedTateY_zpow_mul_parameter parameterNeZero m (u : K)])

@[simp] theorem normalizedTateQuotientPoint_mk (q : K)
    (parameterNeZero : q ≠ 0) (hdata : TateNormalizedPointData q)
    (u : ↥(coordinateParameterDomain q)) :
    normalizedTateQuotientPoint q parameterNeZero hdata (Quotient.mk _ u) =
      WeierstrassCurve.Affine.Point.some
        (normalizedTateX q (u : K)) (normalizedTateY q (u : K)) (hdata u) :=
  rfl

/-- Exact remaining canonical point-map gap: injectivity and coverage of the
nonzero curve points by normalized-coordinate parameters. -/
def TateUniformizationNormalizedPointMapGap (q : K)
    (parameterNeZero : q ≠ 0) (hdata : TateNormalizedPointData q) : Prop :=
  Function.Injective (normalizedTateQuotientPoint q parameterNeZero hdata) ∧
    ∀ P : (weierstrassCurve K q).toAffine.Point, P ≠ 0 →
      ∃ w : TateParameterQuotient q parameterNeZero,
        normalizedTateQuotientPoint q parameterNeZero hdata w = P

end

end LeanFormal.IUT.TateCurve
