import LeanFormal.IUT.Foundations.AlgebraicGeometry.ChartQuotientRestrictionNaturality
import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorFixedPointsLocalizationNaturality
/-!
# Projection-level proof of chart/overlap restriction naturality

Reduces the restriction square to its two pullback projections and the
`pullbackSpecIso` projection lemmas.  The remaining algebra input is the
fixed-point naturality square, isolated in one explicit theorem.
-/

noncomputable section

open scoped TensorProduct
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ABCBridge.TensorFixedPointsLocalizationNaturalityProof

universe u

open ABCBridge.TensorFixedPointsLocalizationNaturality
open ABCBridge.ChartQuotientRestrictionNaturality

variable {R A G : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G]
  [MulSemiringAction G A] [SMulCommClass G R A]

/-- First projection of the chart restriction map. -/
@[reassoc]
theorem chartRestrictionMap_fst (f g : R) :
    chartRestrictionMap (R := R) (A := A) (G := G) f g ≫
        pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap R (chartRing f))))
          (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))) =
      pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap R (overlapRing f g))))
          (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))) ≫
        overlapChartMap (R := R) (A := A) (G := G) f g :=
  by simp [chartRestrictionMap, overlapChartMap]

/-- Second projection of the chart restriction map. -/
@[reassoc]
theorem chartRestrictionMap_snd (f g : R) :
    chartRestrictionMap (R := R) (A := A) (G := G) f g ≫
        pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap R (chartRing f))))
          (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))) =
      pullback.snd
          (Spec.map (CommRingCat.ofHom (algebraMap R (overlapRing f g))))
          (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))) :=
  by simp [chartRestrictionMap, overlapChartMap]

/-- First projection of the chart quotient restriction iso. -/
@[reassoc]
theorem chartQuotientRestrictionIso_hom_fst (f : R) :
    (chartQuotientRestrictionIso (R := R) (A := A) (G := G) f).hom ≫
        pullback.fst
          (Spec.map (CommRingCat.ofHom (algebraMap R (chartRing f))))
          (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap R (FixedPoints.subalgebra (chartRing f)
          (chartRing f ⊗[R] A) G))) ≫
        (Scheme.Spec.mapIso (chartFixedPointEquiv (R := R) (A := A) (G := G) f).toRingEquiv.toCommRingCatIso.op).hom :=
  by
  simp [chartQuotientRestrictionIso, AlgebraicGeometry.pullbackSpecIso_hom_fst,
    Scheme.Spec.mapIso, chartFixedPointEquiv]

/-- The isolated algebra naturality input: the chart fixed-point equivalence
commutes with base change to the overlap. -/
theorem chartFixedPointEquiv_algebra_naturality (f g : R)
    (x : chartRing f ⊗[R] FixedPoints.subalgebra R A G) :
    fixedPointExtensionAlgHom (R := R) (A := A) (G := G) f g
        (chartFixedPointEquiv (R := R) (A := A) (G := G) f x) =
      overlapFixedPointEquiv (R := R) (A := A) (G := G) f g
        (Algebra.TensorProduct.map
          (chartToOverlap (R := R) (A := A) (G := G) f g)
          (AlgHom.id R (FixedPoints.subalgebra R A G)) x) :=
  chartFixedPointEquiv_naturality (R := R) (A := A) (G := G) f g x

/-- Chart/overlap restriction square, reduced to the algebra naturality input. -/
theorem chartQuotientRestriction_square (f g : R) :
    chartRestrictionMap (R := R) (A := A) (G := G) f g ≫
        chartQuotientRestrictionIso (R := R) (A := A) (G := G) f =
      overlapQuotientRestrictionIso (R := R) (A := A) (G := G) f g ≫
        fixedPointExtensionSpecMap (R := R) (A := A) (G := G) f g := by
  apply pullback.hom_ext
  · rw [Category.assoc, chartQuotientRestrictionIso_hom_fst,
      chartRestrictionMap_fst, Category.assoc]
    simp [overlapQuotientRestrictionIso, fixedPointExtensionSpecMap,
      chartFixedPointEquiv_algebra_naturality]
  · rw [Category.assoc, chartRestrictionMap_snd]
    simp [chartQuotientRestrictionIso, overlapQuotientRestrictionIso,
      fixedPointExtensionSpecMap, AlgebraicGeometry.pullbackSpecIso,
      chartFixedPointEquiv_algebra_naturality]

end ABCBridge.TensorFixedPointsLocalizationNaturalityProof