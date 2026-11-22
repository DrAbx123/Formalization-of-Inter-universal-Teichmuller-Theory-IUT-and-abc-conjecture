import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientTransitionData
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientGluedCover
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Consumer for the global affine quotient gluing data

This file packages the actual scheme-level glued quotient from a compatible
`AffineLocalQuotientPreglueData`: the glued map is a finite etale cover, and
the chart-level descent/universal property is exposed for the global quotient
consumer.  The transition/overlap data is supplied by
`GlobalQuotientTransitionData`; this file does not fabricate a cover or a card.
-/
namespace ABCBridge.GlobalQuotientGluingConsumer

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

universe u

variable {S : Scheme.{u}}

/-- A compatible affine quotient preglue package: the chart compatibility and
the glued-map finiteness are the actual inputs of the gluing theorem. -/
structure CompatibleAffineQuotientGluingData (S : Scheme.{u}) where
  preglue : AffineLocalQuotientPreglueData S
  compatible : ∀ i j,
    pullback.fst ((preglue.toSchemeGlueData).ι i)
        ((preglue.toSchemeGlueData).ι j) ≫ preglue.q i =
      pullback.snd ((preglue.toSchemeGlueData).ι i)
        ((preglue.toSchemeGlueData).ι j) ≫ preglue.q j
  finite : IsFinite (preglue.gluedMapOfCompatible compatible)

/-- The actual global quotient cover obtained by gluing the affine quotient
charts. -/
noncomputable def globalQuotientCover
    (D : CompatibleAffineQuotientGluingData S) : FiniteEtaleCover S :=
  D.preglue.toFiniteEtaleCoverOfIsFinite D.compatible D.finite

/-- Its structure map is the glued quotient map from the affine charts. -/
theorem globalQuotientCover_structureMap
    (D : CompatibleAffineQuotientGluingData S) :
    FiniteEtaleCover.structureMap (globalQuotientCover D) =
      D.preglue.gluedMapOfCompatible D.compatible :=
  rfl

/-- The global quotient cover is etale over the base. -/
theorem globalQuotientCover_etale
    (D : CompatibleAffineQuotientGluingData S) :
    Etale (FiniteEtaleCover.structureMap (globalQuotientCover D)) :=
  D.preglue.gluedMapOfCompatible_etale D.compatible

/-- Descent from compatible chart morphisms to the glued quotient. -/
noncomputable def globalQuotientDesc
    (D : CompatibleAffineQuotientGluingData S) (Z : Scheme.{u})
    (f : ∀ i : D.preglue.J, D.preglue.U i ⟶ Z)
    (hf : ∀ i j : D.preglue.J,
      pullback.fst ((D.preglue.toSchemeGlueData).ι i)
          ((D.preglue.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.preglue.toSchemeGlueData).ι i)
          ((D.preglue.toSchemeGlueData).ι j) ≫ f j) :
    D.preglue.glued ⟶ Z :=
  D.preglue.descOfCompatible Z f hf

/-- Restriction of the descended map to each affine quotient chart. -/
theorem globalQuotientDesc_ι
    (D : CompatibleAffineQuotientGluingData S) (Z : Scheme.{u})
    (f : ∀ i : D.preglue.J, D.preglue.U i ⟶ Z)
    (hf : ∀ i j : D.preglue.J,
      pullback.fst ((D.preglue.toSchemeGlueData).ι i)
          ((D.preglue.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.preglue.toSchemeGlueData).ι i)
          ((D.preglue.toSchemeGlueData).ι j) ≫ f j)
    (i : D.preglue.J) :
    (D.preglue.toSchemeGlueData).ι i ≫
        globalQuotientDesc D Z f hf = f i :=
  D.preglue.descOfCompatible_ι Z f hf i

/-- Uniqueness of the descended map. -/
theorem globalQuotientDesc_unique
    (D : CompatibleAffineQuotientGluingData S) (Z : Scheme.{u})
    (f : ∀ i : D.preglue.J, D.preglue.U i ⟶ Z)
    (hf : ∀ i j : D.preglue.J,
      pullback.fst ((D.preglue.toSchemeGlueData).ι i)
          ((D.preglue.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.preglue.toSchemeGlueData).ι i)
          ((D.preglue.toSchemeGlueData).ι j) ≫ f j)
    (u : D.preglue.glued ⟶ Z)
    (hu : ∀ i : D.preglue.J,
      (D.preglue.toSchemeGlueData).ι i ≫ u = f i) :
    u = globalQuotientDesc D Z f hf :=
  D.preglue.descOfCompatible_unique Z f hf u hu


section GlobalQuotientFacts

/-- The global quotient structure map is finite. -/
theorem globalQuotientCover_finite
    (D : CompatibleAffineQuotientGluingData S) :
    IsFinite (FiniteEtaleCover.structureMap (globalQuotientCover D)) :=
  D.finite

/-- The structure map of the global quotient cover restricts to the quotient
chart maps on the glued affine charts. -/
theorem globalQuotientCover_structureMap_ι
    (D : CompatibleAffineQuotientGluingData S) (i : D.preglue.J) :
    (D.preglue.toSchemeGlueData).ι i ≫
        FiniteEtaleCover.structureMap (globalQuotientCover D) = D.preglue.q i :=
  D.preglue.gluedMapOfCompatible_ι D.compatible i

/-- The descended map is the unique compatible extension of the chart maps. -/
theorem globalQuotientDesc_unique'
    (D : CompatibleAffineQuotientGluingData S) (Z : Scheme.{u})
    (f : ∀ i : D.preglue.J, D.preglue.U i ⟶ Z)
    (hf : ∀ i j : D.preglue.J,
      pullback.fst ((D.preglue.toSchemeGlueData).ι i)
          ((D.preglue.toSchemeGlueData).ι j) ≫ f i =
        pullback.snd ((D.preglue.toSchemeGlueData).ι i)
          ((D.preglue.toSchemeGlueData).ι j) ≫ f j)
    (u : D.preglue.glued ⟶ Z)
    (hu : ∀ i : D.preglue.J,
      (D.preglue.toSchemeGlueData).ι i ≫ u = f i) :
    u = globalQuotientDesc D Z f hf :=
  globalQuotientDesc_unique D Z f hf u hu

end GlobalQuotientFacts

end ABCBridge.GlobalQuotientGluingConsumer
