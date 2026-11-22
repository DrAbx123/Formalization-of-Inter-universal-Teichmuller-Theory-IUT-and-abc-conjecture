import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorFixedPointsBaseChange
import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorEqualizerFixedPoints
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Flat.Localization

/-!
# M1 localization naturality and chart restriction

Specializes the equalizer/M1 naturality square to the chart tower
R -> R[1/f] -> R[1/(f*g)].  The chart quotient restriction is then the
Spec of the localized fixed-point algebra equivalence.
-/

noncomputable section

open scoped TensorProduct
open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits CategoryTheory.Limits

namespace ABCBridge.TensorFixedPointsLocalizationNaturality

universe u

variable {R A G : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G]
  [MulSemiringAction G A] [SMulCommClass G R A]

/-- The affine chart `Spec R[1/f]`. -/
abbrev chartRing (f : R) : Type u := Localization.Away f

/-- The overlap chart `Spec R[1/(f*g)]`. -/
abbrev overlapRing (f g : R) : Type u := Localization.Away (f * g)

/-- The canonical ring map from the `f`-chart to the `(f*g)`-overlap. -/
noncomputable def chartToOverlap (f g : R) : chartRing f →ₐ[R] overlapRing f g :=
  letI : Algebra R (chartRing f) := inferInstance
  letI : Algebra R (overlapRing f g) := inferInstance
  { toRingHom := IsLocalization.Away.awayToAwayRight f g
    commutes' := fun r => by
      change IsLocalization.Away.awayToAwayRight f g (algebraMap R (chartRing f) r) =
        algebraMap R (overlapRing f g) r
      exact IsLocalization.Away.awayToAwayRight_eq f g r }

/-- The fixed-point algebra equivalence for the chart ring. -/
noncomputable def chartFixedPointEquiv (f : R) :
    chartRing f ⊗[R] FixedPoints.subalgebra R A G ≃ₐ[chartRing f]
      FixedPoints.subalgebra (chartRing f) (chartRing f ⊗[R] A) G :=
  letI : Algebra R (chartRing f) := inferInstance
  letI : Module.Flat R (chartRing f) := IsLocalization.flat (chartRing f) (Submonoid.powers f)
  letI : Algebra R (FixedPoints.subalgebra (chartRing f) (chartRing f ⊗[R] A) G) :=
    inferInstance
  M1Final.tensorFixedPointsAlgEquiv (R := R) (A := A) (G := G)
    (T := chartRing f)

/-- The fixed-point algebra equivalence for the overlap ring. -/
noncomputable def overlapFixedPointEquiv (f g : R) :
    overlapRing f g ⊗[R] FixedPoints.subalgebra R A G ≃ₐ[overlapRing f g]
      FixedPoints.subalgebra (overlapRing f g) (overlapRing f g ⊗[R] A) G :=
  letI : Algebra R (overlapRing f g) := inferInstance
  letI : Module.Flat R (overlapRing f g) := IsLocalization.flat (overlapRing f g) (Submonoid.powers (f * g))
  letI : Algebra R (FixedPoints.subalgebra (overlapRing f g)
    (overlapRing f g ⊗[R] A) G) := inferInstance
  M1Final.tensorFixedPointsAlgEquiv (R := R) (A := A) (G := G)
    (T := overlapRing f g)

/-- Chart restriction identification: the pullback of the global quotient along
the chart is the quotient of the localized algebra. -/
noncomputable def chartQuotientRestrictionIso (f : R) :
    pullback (C := Scheme.{u})
        (Spec.map (CommRingCat.ofHom (algebraMap R (chartRing f))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G) ))) ≅ Spec (CommRingCat.of (FixedPoints.subalgebra (chartRing f)
        (chartRing f ⊗[R] A) G)) :=
  (AlgebraicGeometry.pullbackSpecIso (R := R) (S := chartRing f)
    (T := FixedPoints.subalgebra R A G)).trans
    (Scheme.Spec.mapIso (chartFixedPointEquiv (R := R) (A := A) (G := G) f).toRingEquiv.toCommRingCatIso.symm.op)

/-- Overlap restriction identification. -/
noncomputable def overlapQuotientRestrictionIso (f g : R) :
    pullback (C := Scheme.{u})
        (Spec.map (CommRingCat.ofHom (algebraMap R (overlapRing f g))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (FixedPoints.subalgebra R A G) ))) ≅ Spec (CommRingCat.of (FixedPoints.subalgebra (overlapRing f g)
        (overlapRing f g ⊗[R] A) G)) :=
  (AlgebraicGeometry.pullbackSpecIso (R := R) (S := overlapRing f g)
    (T := FixedPoints.subalgebra R A G)).trans
    (Scheme.Spec.mapIso (overlapFixedPointEquiv (R := R) (A := A) (G := G) f g).toRingEquiv.toCommRingCatIso.symm.op)

/- Localization naturality is not asserted here: it is the M1 square
   `chartFixedPointEquiv` vs `overlapFixedPointEquiv` after restricting the
   chart; the proof is the prerequisite still being repaired. -/

end ABCBridge.TensorFixedPointsLocalizationNaturality
