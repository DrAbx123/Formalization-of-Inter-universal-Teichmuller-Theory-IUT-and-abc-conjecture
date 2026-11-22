import LeanFormal.IUT.Foundations.AlgebraicGeometry.ChartQuotientRestrictionNaturality

/-!
# Triple-overlap coherence for quotient restriction charts

Defines the triple chart `R[1/(f*g*h)]` and proves that the two-step transition
through an intermediate overlap agrees with the direct chart-to-triple transition.
Uses pullback hom-ext and `pullbackSpecIso` projection naturality.
-/

noncomputable section

open scoped TensorProduct
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ABCBridge.TripleOverlapCoherence

universe u

open ABCBridge.TensorFixedPointsLocalizationNaturality
open ABCBridge.ChartQuotientRestrictionNaturality

variable {R A G : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G]
  [MulSemiringAction G A] [SMulCommClass G R A]

/-- The triple chart ring `R[1/(f*g*h)]`. -/
abbrev tripleRing (f g h : R) : Type u := Localization.Away (f * g * h)

instance tripleAlgebra (f g h : R) : Algebra R (tripleRing f g h) := inferInstance

/-- The fixed-point equivalence on the triple chart. -/
noncomputable def tripleFixedPointEquiv (f g h : R) :
    tripleRing f g h ⊗[R] FixedPoints.subalgebra R A G ≃ₐ[tripleRing f g h]
      FixedPoints.subalgebra (tripleRing f g h)
        (tripleRing f g h ⊗[R] A) G :=
  letI : Algebra R (tripleRing f g h) := inferInstance
  letI : Algebra R (FixedPoints.subalgebra (tripleRing f g h)
      (tripleRing f g h ⊗[R] A) G) := inferInstance
  M1Final.tensorFixedPointsAlgEquiv (R := R) (A := A) (G := G)
    (T := tripleRing f g h)

/-- The quotient-restriction chart at the triple overlap. -/
noncomputable def tripleQuotientRestrictionIso (f g h : R) :
    pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (tripleRing f g h))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))) →
      Spec (CommRingCat.of (FixedPoints.subalgebra (tripleRing f g h)
        (tripleRing f g h ⊗[R] A) G)) :=
  (AlgebraicGeometry.pullbackSpecIso (R := R) (S := tripleRing f g h)
      (T := FixedPoints.subalgebra R A G)).trans
    (Scheme.Spec.mapIso (tripleFixedPointEquiv (R := R) (A := A) (G := G) f g h).toRingEquiv.toCommRingCatIso.op)

/-- First step: chart `f` to overlap `f*g`. -/
noncomputable def chartToOverlapPullbackMap (f g : R) :
    pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (overlapRing f g))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))) →
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (chartRing f))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))) :=
  chartRestrictionMap (R := R) (A := A) (G := G) f g

/-- Second step: overlap `f*g` to triple `(f*g)*h`. -/
noncomputable def overlapToTriplePullbackMap (f g h : R) :
    pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (tripleRing f g h))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))) →
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (overlapRing f g))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))) :=
  pullback.map _ _ _ _
    (Spec.map (CommRingCat.ofHom
      (chartToOverlap (R := R) (A := A) (G := G) (f * g) h).toRingHom))
    (AlgHom.id R (FixedPoints.subalgebra R A G))
    (AlgHom.id R (FixedPoints.subalgebra R A G))
    (by simp [chartToOverlap, IsScalarTower.algebraMap_apply])

/-- The two-step chart-to-triple map. -/
noncomputable def chartToTripleTwoStep (f g h : R) :
    pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (tripleRing f g h))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))) →
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (chartRing f))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))) :=
  chartToOverlapPullbackMap (R := R) (A := A) (G := G) f g ≫
    overlapToTriplePullbackMap (R := R) (A := A) (G := G) f g h

/-- Direct chart-to-triple map, using the `f` and `g*h` factorization. -/
noncomputable def chartToTripleDirect (f g h : R) :
    pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (tripleRing f g h))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))) →
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (chartRing f))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))) :=
  chartToOverlapPullbackMap (R := R) (A := A) (G := G) f (g * h) ≫
    overlapToTriplePullbackMap (R := R) (A := A) (G := G) (f * (g * h)) h

/-- Triple cocycle: the two-step and direct chart-to-triple maps agree after
the triple quotient identification. -/
theorem chartToTriple_cocycle (f g h : R) :
    chartToTripleTwoStep (R := R) (A := A) (G := G) f g h ≫
        tripleQuotientRestrictionIso (R := R) (A := A) (G := G) f g h =
      chartToTripleDirect (R := R) (A := A) (G := G) f g h ≫
        tripleQuotientRestrictionIso (R := R) (A := A) (G := G) f g h := by
  apply Iso.ext
  apply pullback.hom_ext
  · simp [chartToTripleTwoStep, chartToTripleDirect, chartToOverlapPullbackMap,
      overlapToTriplePullbackMap, chartQuotientRestrictionIso,
      tripleQuotientRestrictionIso, AlgebraicGeometry.pullbackSpecIso]
  · simp [chartToTripleTwoStep, chartToTripleDirect, chartToOverlapPullbackMap,
      overlapToTriplePullbackMap, chartQuotientRestrictionIso,
      tripleQuotientRestrictionIso, AlgebraicGeometry.pullbackSpecIso]

end ABCBridge.TripleOverlapCoherence