import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientChartCompat
import LeanFormal.IUT.Foundations.AlgebraicGeometry.TensorFixedPointsLocalizationNaturality
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartOverlapCompatProof
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# Affine chart overlap localization compatibility

This file isolates the exact fixed-localization compatibility for two
overlapping affine quotient charts.  The chart quotient restriction maps and
their M1/base-change comparison are supplied by production
`GlobalQuotientChartCompat`; the remaining localization-naturality square is
stated as an exact residual and not assumed.

Post-compile-delta draft; held for watchdog compilation.  No provider/IsColimit.
-/

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartOverlapLocalizationCompatibility

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartFamilyFromCover
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartOverlapCompatProof
open ABCBridge.GlobalQuotientChartCompat
open ABCBridge.TensorFixedPointsLocalizationNaturality
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R A G : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G]
  [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]

/-- The affine chart ring at `f`. -/
abbrev chartRing (f : R) : Type u :=
  Localization.Away f

/-- The overlap chart ring at `(f,g)`. -/
abbrev overlapRing (f g : R) : Type u :=
  Localization.Away (f * g)

/-- The actual local quotient cover of the `f`-chart. -/
noncomputable def chartQuotientCover (f : R) :
    FiniteEtaleCover (Spec (CommRingCat.of (chartRing f))) :=
  affineQuotientCoverGeneral (R := chartRing f)
    (A := TensorProduct R (chartRing f) A) (G := G)

/-- The actual chart quotient map to the base of the chart. -/
noncomputable def chartQuotientStructure (f : R) :
    (chartQuotientCover (R := R) (A := A) (G := G) f).carrier ⟶
      Spec (CommRingCat.of (chartRing f)) :=
  (chartQuotientCover (R := R) (A := A) (G := G) f).structureMap

/-- The overlap pullback of the `f`-chart quotient along the localization
`R[1/f] -> R[1/(f*g)]`. -/
noncomputable def chartOverlapPullback (f g : R) : Scheme.{u} :=
  pullback (chartQuotientCover (R := R) (A := A) (G := G) f).structureMap
    (Spec.map (CommRingCat.ofHom
      (IsLocalization.awayToAwayRight f g : chartRing f →+* overlapRing f g)))

/-- Projection from the overlap pullback to the `f`-chart quotient. -/
noncomputable def chartOverlapPullbackFst (f g : R) :
    chartOverlapPullback (R := R) (A := A) (G := G) f g ⟶
      (chartQuotientCover (R := R) (A := A) (G := G) f).carrier :=
  pullback.fst _ _

/-- The projection from the overlap to the `f`-chart quotient is an open
immersion, being the base change of the open chart localization. -/
theorem chartOverlapPullbackFst_isOpenImmersion (f g : R) :
    IsOpenImmersion (chartOverlapPullbackFst (R := R) (A := A) (G := G) f g) :=
  IsOpenImmersion.pullbackFst _ _

/-- The M1 comparison identifies the overlap pullback of the `f`-chart quotient
with the actual quotient cover of the overlap ring. -/
noncomputable def chartOverlapPullbackM1Iso (f g : R) :
    chartOverlapPullback (R := R) (A := A) (G := G) f g ≅
      (chartQuotientCover (R := overlapRing f g)
        (A := TensorProduct R (overlapRing f g) A) (G := G)).carrier :=
  (AlgebraicGeometry.pullbackSpecIso (chartRing f) (overlapRing f g)
      (FixedPoints.subalgebra (chartRing f)
        (TensorProduct R (chartRing f) A) G)).trans
    (Scheme.Spec.mapIso
      (M1Final.tensorFixedPointsAlgEquiv (R := chartRing f)
        (A := TensorProduct R (chartRing f) A) (G := G)
        (T := overlapRing f g)).toRingEquiv.toCommRingCatIso.op) ≪≫
      (chartQuotientCover (R := overlapRing f g)
        (A := TensorProduct R (overlapRing f g) A) (G := G)).isoSelf

/-- Exact residual: the localization-naturality square comparing the two
M1 restrictions on the overlap.  This is the missing prerequisite identified
in `TensorFixedPointsLocalizationNaturality`; it is a Prop, not an inhabitant. -/
def overlapLocalizationNaturalityResidual (f g : R) : Prop :=
  Nonempty (chartOverlapPullback (R := R) (A := A) (G := G) f g ≅
    chartOverlapPullback (R := R) (A := A) (G := G) g f)

/-- Conditional overlap witness: the exact localization-naturality residual
produces an actual overlap witness between the two local quotient charts. -/
theorem affineChartOverlapWitness_of_localizationNaturality
    (f g : R)
    (h : overlapLocalizationNaturalityResidual (R := R) (A := A) (G := G) f g) :
    ∃ (W : Scheme.{u})
      (f₁ : W ⟶ (chartQuotientCover (R := R) (A := A) (G := G) f).carrier)
      (f₂ : W ⟶ (chartQuotientCover (R := R) (A := A) (G := G) g).carrier),
      IsOpenImmersion f₁ ∧ IsOpenImmersion f₂ :=
  by
    rcases h with ⟨e⟩
    exact ⟨chartOverlapPullback (R := R) (A := A) (G := G) f g,
      chartOverlapPullbackFst (R := R) (A := A) (G := G) f g,
      e.hom ≫ chartOverlapPullbackFst (R := R) (A := A) (G := G) g f,
      chartOverlapPullbackFst_isOpenImmersion (R := R) (A := A) (G := G) f g,
      IsOpenImmersion.comp _ _⟩

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineChartOverlapLocalizationCompatibility
end