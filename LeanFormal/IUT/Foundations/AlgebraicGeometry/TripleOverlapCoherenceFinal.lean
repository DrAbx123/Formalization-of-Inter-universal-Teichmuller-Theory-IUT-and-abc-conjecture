import LeanFormal.IUT.Foundations.AlgebraicGeometry.TripleOverlapCoherence
import LeanFormal.IUT.Foundations.AlgebraicGeometry.TripleLocalizationAssociativity
/-!
# Final triple-overlap coherence

Redefines the direct chart-to-triple map through `overlapRing f (g*h)` and the
associativity algebra equivalence, then compares it with the two-step map by
`pullback.hom_ext` and localization ring-hom extensionality.
-/

noncomputable section

open scoped TensorProduct
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace ABCBridge.TripleOverlapCoherenceFinal

universe u

open ABCBridge.TensorFixedPointsLocalizationNaturality
open ABCBridge.ChartQuotientRestrictionNaturality
open ABCBridge.TripleOverlapCoherence
open ABCBridge.TripleLocalizationAssociativity

variable {R A G : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G]
  [MulSemiringAction G A] [SMulCommClass G R A]

/-- The base map from the overlap `f*(g*h)` to the triple chart, obtained from
the associativity algebra equivalence. -/
noncomputable def overlapAssocToTripleSchemeMap (f g h : R) :
    Spec (CommRingCat.of (Localization.Away (f * (g * h)))) →
      Spec (CommRingCat.of (Localization.Away (f * g * h))) :=
  (tripleChartAssocIso (R := R) f g h).hom

/-- Pullback map from the `f*(g*h)` overlap to the triple chart. -/
noncomputable def overlapAssocToTriplePullbackMap (f g h : R) :
    pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (tripleRing f g h))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))) →
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (overlapRing f (g * h)))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))) :=
  pullback.map _ _ _ _
    (overlapAssocToTripleSchemeMap (R := R) f g h)
    (AlgHom.id R (FixedPoints.subalgebra R A G))
    (AlgHom.id R (FixedPoints.subalgebra R A G))
    (by
      simp [overlapAssocToTripleSchemeMap, tripleChartAssocIso,
        awayMulAssocAlgEquiv_algebraMap])

/-- Direct chart-to-triple map through the `f*(g*h)` overlap and associativity. -/
noncomputable def chartToTripleDirectAssoc (f g h : R) :
    pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (tripleRing f g h))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))) →
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (chartRing f))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G)))) :=
  chartToOverlapPullbackMap (R := R) (A := A) (G := G) f (g * h) ≫
    overlapAssocToTriplePullbackMap (R := R) (A := A) (G := G) f g h

/-- The direct associativity map agrees with the two-step map. -/
theorem chartToTripleDirectAssoc_eq_twoStep (f g h : R) :
    chartToTripleDirectAssoc (R := R) (A := A) (G := G) f g h =
      chartToTripleTwoStep (R := R) (A := A) (G := G) f g h := by
  apply pullback.hom_ext
  · -- first projection: both are the chart projection
    simp [chartToTripleDirectAssoc, chartToTripleTwoStep,
      chartToOverlapPullbackMap, overlapToTriplePullbackMap,
      overlapAssocToTriplePullbackMap, overlapAssocToTripleSchemeMap,
      tripleChartAssocIso, awayMulAssocAlgEquiv]
  · -- second projection: both are the identity on the quotient fixed point
    simp [chartToTripleDirectAssoc, chartToTripleTwoStep,
      chartToOverlapPullbackMap, overlapToTriplePullbackMap,
      overlapAssocToTriplePullbackMap, overlapAssocToTripleSchemeMap,
      tripleChartAssocIso, awayMulAssocAlgEquiv]

/-- Final triple cocycle: both orders agree with the direct triple identification. -/
theorem chartToTriple_cocycle_final (f g h : R) :
    chartToTripleTwoStep (R := R) (A := A) (G := G) f g h ≫
        tripleQuotientRestrictionIso (R := R) (A := A) (G := G) f g h =
      chartToTripleDirectAssoc (R := R) (A := A) (G := G) f g h ≫
        tripleQuotientRestrictionIso (R := R) (A := A) (G := G) f g h := by
  rw [chartToTripleDirectAssoc_eq_twoStep]

end ABCBridge.TripleOverlapCoherenceFinal