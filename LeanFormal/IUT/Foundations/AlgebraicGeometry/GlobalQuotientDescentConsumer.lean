import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientPreglueData
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingConsumer
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Descent consumer for the localized global quotient

This file consumes the localized affine quotient preglue data as an actual
scheme-level quotient cover.  It packages the global quotient cover, its
structure-map restrictions to the affine charts, and the descended map from
compatible chart maps.

The only external input is the overlap scheme/cocycle data of
`GlobalQuotientPreglueData`; no cover or inhabitant is fabricated here.
-/
namespace ABCBridge.GlobalQuotientDescentConsumer

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineGeneralQuotientG2Consumer
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open ABCBridge.GlobalQuotientTransitionData
open ABCBridge.GlobalQuotientCocycle
open ABCBridge.GlobalQuotientPreglueData
open ABCBridge.GlobalQuotientGluingConsumer

universe u

variable {R : Type u} [CommRing R] {A G : Type u} [CommRing A] [Algebra R A]
  [Group G] [Fintype G] [DecidableEq G] [MulSemiringAction G A] [SMulCommClass G R A]
  [Algebra.Etale R A] [Module.Finite R A]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  (t : ι → R)

/-- Actual compatible affine quotient gluing data obtained from the localized
quotient charts, overlap maps and the global chart maps. -/
noncomputable def localizedCompatibleGluingData
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i))
    (hq : ∀ i j,
      pullback.fst (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι i)
          (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι j) ≫ q i =
        pullback.snd (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι i)
          (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι j) ≫ q j)
    (hfin : IsFinite ((toPreglueData (A := A) (G := G) t M S q q_etale).gluedMapOfCompatible hq)) :
    CompatibleAffineQuotientGluingData S :=
  { preglue := toPreglueData (A := A) (G := G) t M S q q_etale
    compatible := hq
    finite := hfin }

/-- The actual global quotient cover from the localized affine charts. -/
noncomputable def localizedGlobalQuotientCover
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i))
    (hq : ∀ i j,
      pullback.fst (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι i)
          (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι j) ≫ q i =
        pullback.snd (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι i)
          (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι j) ≫ q j)
    (hfin : IsFinite ((toPreglueData (A := A) (G := G) t M S q q_etale).gluedMapOfCompatible hq)) :
    FiniteEtaleCover S :=
  globalQuotientCover
    (localizedCompatibleGluingData (A := A) (G := G) t M S q q_etale hq hfin)

/-- The global quotient structure map restricts to the localized quotients on
the affine charts. -/
theorem localizedGlobalQuotientCover_structureMap_ι
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i))
    (hq : ∀ i j,
      pullback.fst (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι i)
          (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι j) ≫ q i =
        pullback.snd (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι i)
          (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι j) ≫ q j)
    (hfin : IsFinite ((toPreglueData (A := A) (G := G) t M S q q_etale).gluedMapOfCompatible hq))
    (i : ι) :
    ((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι i ≫
        FiniteEtaleCover.structureMap
          (localizedGlobalQuotientCover (A := A) (G := G) t M S q q_etale hq hfin) = q i :=
  globalQuotientCover_structureMap_ι
    (localizedCompatibleGluingData (A := A) (G := G) t M S q q_etale hq hfin) i


section LocalizedGlobalQuotientFacts

theorem localizedGlobalQuotientCover_structureMap
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i))
    (hq : ∀ i j,
      pullback.fst (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι i)
          (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι j) ≫ q i =
        pullback.snd (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι i)
          (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι j) ≫ q j)
    (hfin : IsFinite ((toPreglueData (A := A) (G := G) t M S q q_etale).gluedMapOfCompatible hq)) :
    FiniteEtaleCover.structureMap
        (localizedGlobalQuotientCover (A := A) (G := G) t M S q q_etale hq hfin) =
      (toPreglueData (A := A) (G := G) t M S q q_etale).gluedMapOfCompatible hq :=
  rfl

theorem localizedGlobalQuotientCover_etale
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i))
    (hq : ∀ i j,
      pullback.fst (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι i)
          (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι j) ≫ q i =
        pullback.snd (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι i)
          (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι j) ≫ q j)
    (hfin : IsFinite ((toPreglueData (A := A) (G := G) t M S q q_etale).gluedMapOfCompatible hq)) :
    Etale (FiniteEtaleCover.structureMap
      (localizedGlobalQuotientCover (A := A) (G := G) t M S q q_etale hq hfin)) :=
  (globalQuotientCover (localizedCompatibleGluingData (A := A) (G := G) t M S q q_etale hq hfin)).structureMap_etale

theorem localizedGlobalQuotientCover_finite
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i))
    (hq : ∀ i j,
      pullback.fst (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι i)
          (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι j) ≫ q i =
        pullback.snd (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι i)
          (((toPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι j) ≫ q j)
    (hfin : IsFinite ((toPreglueData (A := A) (G := G) t M S q q_etale).gluedMapOfCompatible hq)) :
    IsFinite (FiniteEtaleCover.structureMap
      (localizedGlobalQuotientCover (A := A) (G := G) t M S q q_etale hq hfin)) :=
  hfin

end LocalizedGlobalQuotientFacts

end ABCBridge.GlobalQuotientDescentConsumer