import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientPreglueData
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientDescentConsumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientGluingConsumer
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Check layer for localized affine quotient preglue data

This file checks the actual fields of the preglue data assembled from the
localized quotient charts and overlap maps: open-immersion, pullback, identity,
transition and cocycle fields, plus the compatibility needed for the glued
quotient.  It is a check/consumer layer, not a new transition construction.
-/
namespace ABCBridge.GlobalQuotientPreglueCheck

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

/-- The checked preglue data from the localized charts and overlap maps. -/
noncomputable def checkedPreglueData
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i)) :
    AffineLocalQuotientPreglueData S :=
  toPreglueData (A := A) (G := G) t M S q q_etale

theorem checkedPreglueData_f_open
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i)) (i j : ι) :
    IsOpenImmersion ((checkedPreglueData (A := A) (G := G) t M S q q_etale).f i j) :=
  M.f_open i j

theorem checkedPreglueData_f_hasPullback
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i)) (i j k : ι) :
    HasPullback ((checkedPreglueData (A := A) (G := G) t M S q q_etale).f i j)
      ((checkedPreglueData (A := A) (G := G) t M S q q_etale).f i k) :=
  M.f_hasPullback i j k

theorem checkedPreglueData_f_id
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i)) (i : ι) :
    IsIso ((checkedPreglueData (A := A) (G := G) t M S q q_etale).f i i) :=
  M.f_id i

theorem checkedPreglueData_t_id
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i)) (i : ι) :
    (checkedPreglueData (A := A) (G := G) t M S q q_etale).t i i = 𝟙 _ :=
  M.t_id i

theorem checkedPreglueData_t_fac
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i)) (i j k : ι) :
    (checkedPreglueData (A := A) (G := G) t M S q q_etale).t' i j k ≫
        pullback.snd _ _ =
      pullback.fst _ _ ≫
        (checkedPreglueData (A := A) (G := G) t M S q q_etale).t i j :=
  M.t_fac i j k

theorem checkedPreglueData_cocycle
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i)) (i j k : ι) :
    (checkedPreglueData (A := A) (G := G) t M S q q_etale).t' i j k ≫
        (checkedPreglueData (A := A) (G := G) t M S q q_etale).t' j k i ≫
        (checkedPreglueData (A := A) (G := G) t M S q q_etale).t' k i j = 𝟙 _ :=
  M.cocycle i j k

theorem checkedPreglueData_q_etale
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i)) (i : ι) :
    Etale ((checkedPreglueData (A := A) (G := G) t M S q q_etale).q i) :=
  q_etale i

section CheckedGlueMap

theorem checkedPreglueData_gluedMap_ι
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i))
    (hq : ∀ i j,
      pullback.fst (((checkedPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι i)
          (((checkedPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι j) ≫ q i =
        pullback.snd (((checkedPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι i)
          (((checkedPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι j) ≫ q j)
    (i : ι) :
    ((checkedPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι i ≫
        (checkedPreglueData (A := A) (G := G) t M S q q_etale).gluedMapOfCompatible hq = q i :=
  (checkedPreglueData (A := A) (G := G) t M S q q_etale).gluedMapOfCompatible_ι hq i

theorem checkedPreglueData_gluedMap_etale
    (M : LocalizedQuotientOverlapMaps (A := A) (G := G) t)
    (S : Scheme.{u})
    (q : ∀ i, (chart (G := G) t i).carrier ⟶ S)
    (q_etale : ∀ i, Etale (q i))
    (hq : ∀ i j,
      pullback.fst (((checkedPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι i)
          (((checkedPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι j) ≫ q i =
        pullback.snd (((checkedPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι i)
          (((checkedPreglueData (A := A) (G := G) t M S q q_etale).toSchemeGlueData).ι j) ≫ q j) :
    Etale ((checkedPreglueData (A := A) (G := G) t M S q q_etale).gluedMapOfCompatible hq) :=
  (checkedPreglueData (A := A) (G := G) t M S q q_etale).gluedMapOfCompatible_etale hq

end CheckedGlueMap

end ABCBridge.GlobalQuotientPreglueCheck