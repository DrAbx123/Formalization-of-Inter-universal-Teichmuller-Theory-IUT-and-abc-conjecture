import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorEqualizerEquivNaturality
import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorFixedPointsLocalizationNaturality

/-!
# M1 localization naturality

Specializes the candidate equalizer/M1 naturality square to the chart tower
R -> R[1/f] -> R[1/(f*g)], and derives the chart-to-overlap restriction square
for the quotient-cover restriction isomorphisms.
-/

noncomputable section

open scoped TensorProduct
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ABCBridge.M1LocalizationNaturality

universe u

open ABCBridge.TensorFixedPointsLocalizationNaturality
open ABCBridge.TensorEqualizerEquivNaturality

variable {R A G : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G]
  [MulSemiringAction G A] [SMulCommClass G R A]

/-- Localize the base at `f`; this is `T`. -/
abbrev chartBase (f : R) : Type u := chartRing f

/-- Localize the base at `f*g`; this is `T'`. -/
abbrev overlapBase (f g : R) : Type u := overlapRing f g

instance chartBaseAlgebra (f : R) : Algebra R (chartBase f) := inferInstance
instance overlapBaseAlgebra (f g : R) : Algebra R (overlapBase f g) := inferInstance

/-- The canonical `T`-algebra structure on the overlap ring. -/
noncomputable instance overlapAlgebraOverChart (f g : R) :
    Algebra (chartBase f) (overlapBase f g) :=
  RingHom.toAlgebra (chartToOverlap (R := R) f g).toRingHom

instance overlapScalarTower (f g : R) :
    IsScalarTower R (chartBase f) (overlapBase f g) :=
  IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R (overlapBase f g) r =
      (chartToOverlap (R := R) f g)
        (algebraMap R (chartBase f) r)
    exact ((chartToOverlap (R := R) f g).commutes r).symm

/-- M1 naturality at the chart tower, obtained from the equalizer naturality
candidate. -/
theorem chartTensorFixedPoints_naturality
    (f g : R)
    (x : overlapBase f g ⊗[chartBase f]
      (chartBase f ⊗[R] FixedPoints.subalgebra R A G)) :
    M1Final.tensorFixedPointsAlgEquiv (R := R) (A := A) (G := G)
        (T := overlapBase f g)
        (Algebra.TensorProduct.cancelBaseChange (R := R) (S := chartBase f)
          (T := overlapBase f g) (A := overlapBase f g)
          (B := FixedPoints.subalgebra R A G) x) =
      fixedPointBaseChange
        (Algebra.TensorProduct.map (AlgHom.id (overlapBase f g) (overlapBase f g))
          (M1Final.tensorFixedPointsAlgEquiv (R := R) (A := A) (G := G)
            (T := chartBase f)).toAlgHom x) :=
  tensorFixedPointsAlgEquiv_naturality (R := R)
    (T := chartBase f) (T' := overlapBase f g)
    (A := A) x

/-- The map of affine charts induced by localizing at `g`. -/
noncomputable def overlapChartMap (f g : R) :
    Spec (CommRingCat.of (overlapBase f g)) ⟶ Spec (CommRingCat.of (chartBase f)) :=
  Spec.map (CommRingCat.ofHom
    (chartToOverlap (R := R) f g).toRingHom)

/-- The induced map on the chart quotient restriction. -/
noncomputable def chartRestrictionMap (f g : R) :
    pullback (C := Scheme)
        (Spec.map (CommRingCat.ofHom (algebraMap R (overlapBase f g))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))) ⟶
      pullback (C := Scheme)
        (Spec.map (CommRingCat.ofHom (algebraMap R (chartBase f))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))) :=
  pullback.map (C := Scheme) _ _ _ _ (overlapChartMap f g) (AlgHom.id R (FixedPoints.subalgebra R A G))
    (AlgHom.id R (FixedPoints.subalgebra R A G))
    (by
      simp [overlapChartMap, chartToOverlap,
        IsScalarTower.algebraMap_apply R (chartBase f) (overlapBase f g)])

/-- Chart-to-overlap restriction naturality: restricting the chart quotient
isomorphism to the overlap agrees with the overlap quotient isomorphism. -/
theorem chartQuotientRestriction_natural (f g : R) :
    chartRestrictionMap f g ≫ chartQuotientRestrictionIso (R := R) (A := A) (G := G) f =
      overlapQuotientRestrictionIso (R := R) (A := A) (G := G) f g ≫
        Spec.map (CommRingCat.ofHom
          (fixedPointBaseChange).toRingHom) := by
  apply Iso.ext
  -- Both sides are determined by the M1 naturality square on the overlap.
  ext x
  simp [chartRestrictionMap, chartQuotientRestrictionIso,
    overlapQuotientRestrictionIso, chartFixedPointEquiv,
    overlapFixedPointEquiv, fixedPointBaseChange,
    chartTensorFixedPoints_naturality]

end ABCBridge.M1LocalizationNaturality
