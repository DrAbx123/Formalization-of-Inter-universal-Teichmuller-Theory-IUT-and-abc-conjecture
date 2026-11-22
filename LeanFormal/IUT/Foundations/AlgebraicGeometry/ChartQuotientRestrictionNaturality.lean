import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorFixedPointsLocalizationNaturality
import LeanFormal.IUT.Foundations.AlgebraicGeometry.M1LocalizationNaturality

/-!
# Chart quotient restriction naturality

Proves that restricting the chart quotient isomorphism to the overlap agrees with
the overlap quotient isomorphism and the fixed-point extension map.  The proof
is by the algebra naturality square, then `Spec`/pullback naturality.
-/

noncomputable section

open scoped TensorProduct
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ABCBridge.ChartQuotientRestrictionNaturality

universe u

open ABCBridge.TensorFixedPointsLocalizationNaturality
open ABCBridge.M1LocalizationNaturality

variable {R A G : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G]
  [MulSemiringAction G A] [SMulCommClass G R A]

/-- Algebra map from the chart fixed-point subalgebra to the overlap one,
induced by base change along `R[1/f] → R[1/(fg)]`. -/
noncomputable def fixedPointExtensionAlgHom (f g : R) :
    FixedPoints.subalgebra (chartRing f) (chartRing f ⊗[R] A) G →ₐ[R]
      FixedPoints.subalgebra (overlapRing f g) (overlapRing f g ⊗[R] A) G :=
  letI : Algebra (chartRing f) (overlapRing f g) :=
    overlapAlgebraOverChart (R := R) (A := A) (G := G) f g
  { toFun := fun x =>
      ⟨Algebra.TensorProduct.map
          (chartToOverlap (R := R) (A := A) (G := G) f g)
          (AlgHom.id R A) (x : chartRing f ⊗[R] A), by
        rw [FixedPoints.mem_subalgebra] at x.property ⊢
        rw [FixedPoints.mem_subalgebra]
        simpa [map_mul, map_add, AlgHom.id_apply] using congrArg
          (Algebra.TensorProduct.map
            (chartToOverlap (R := R) (A := A) (G := G) f g)
            (AlgHom.id R A)) x.property⟩
    map_one' := by
      ext
      simp
    map_mul' := by
      intro x y
      ext
      simp
    map_zero' := by
      ext
      simp
    map_add' := by
      intro x y
      ext
      simp
    commutes' := by
      intro r
      ext
      simp [chartToOverlap] }

/-- Algebra naturality of the M1 fixed-point equivalence under the chart-to-overlap
base change. -/
theorem chartFixedPointEquiv_naturality (f g : R)
    (x : chartRing f ⊗[R] FixedPoints.subalgebra R A G) :
    fixedPointExtensionAlgHom (R := R) (A := A) (G := G) f g
        ((chartFixedPointEquiv (R := R) (A := A) (G := G) f) x) =
      (overlapFixedPointEquiv (R := R) (A := A) (G := G) f g)
        (Algebra.TensorProduct.map
          (chartToOverlap (R := R) (A := A) (G := G) f g)
          (AlgHom.id R (FixedPoints.subalgebra R A G)) x) := by
  ext
  simp [fixedPointExtensionAlgHom, chartFixedPointEquiv, overlapFixedPointEquiv,
    M1Final.tensorFixedPointsAlgEquiv, AlgHom.comp_apply]

/-- The bottom map between the localized fixed-point quotients. -/
noncomputable def fixedPointExtensionSpecMap (f g : R) :
    Spec (CommRingCat.of (FixedPoints.subalgebra (overlapRing f g)
      (overlapRing f g ⊗[R] A) G)) →
      Spec (CommRingCat.of (FixedPoints.subalgebra (chartRing f)
        (chartRing f ⊗[R] A) G)) :=
  Spec.map (CommRingCat.ofHom
    (fixedPointExtensionAlgHom (R := R) (A := A) (G := G) f g).toRingHom)

/-- The restriction square on the affine quotient charts. -/
theorem chartQuotientRestriction_natural (f g : R) :
    chartRestrictionMap (R := R) (A := A) (G := G) f g ≫
        chartQuotientRestrictionIso (R := R) (A := A) (G := G) f =
      overlapQuotientRestrictionIso (R := R) (A := A) (G := G) f g ≫
        fixedPointExtensionSpecMap (R := R) (A := A) (G := G) f g := by
  apply Iso.ext
  apply pullback.hom_ext
  · -- first projection
    simp [chartRestrictionMap, chartQuotientRestrictionIso,
      overlapQuotientRestrictionIso, fixedPointExtensionSpecMap,
      AlgebraicGeometry.pullbackSpecIso, chartFixedPointEquiv_naturality]
  · -- second projection
    simp [chartRestrictionMap, chartQuotientRestrictionIso,
      overlapQuotientRestrictionIso, fixedPointExtensionSpecMap,
      AlgebraicGeometry.pullbackSpecIso, chartFixedPointEquiv_naturality]

end ABCBridge.ChartQuotientRestrictionNaturality