import LeanFormal.IUT.Foundations.AlgebraicGeometry.FixedLocalizationAction
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal
import Mathlib.Tactic

/-!
# Affine-local finite presentation of fixed-point algebras

Without Noetherian hypotheses, finite presentation is checked affine-locally.
FixedLocalizationAction.awayFixedPointsEquiv identifies the localization
A_f with the fixed points of B_f under the induced action.  The theorem below
takes the local fixed-point algebras as localization data and applies the
affine-local criterion for Algebra.FinitePresentation.

The local IsLocalization/finite-presentation hypotheses are explicit: they are
exactly what the localization descent supplies.  No Noetherian assumption is used.
-/

open LeanFormal.N8.FixedLocalizationAction

namespace ABCBridge.InvariantsFinitePresentationGeneral

noncomputable section

universe u v w

variable {R : Type u} {A : Type v} {B : Type w} {G : Type*}
  [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
  [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

/-- Affine-local criterion for finite presentation of A over R: it suffices
to check finite presentation after inverting a family of elements covering A. -/
theorem affineLocal_finitePresentation
    {ι : Type*} [Finite ι] (s : ι → A)
    (hs : Ideal.span (Set.range s) = ⊤)
    (T : ι → Type*) [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    [∀ i, Algebra A (T i)] [∀ i, IsScalarTower R A (T i)]
    [∀ i, IsLocalization.Away (s i) (T i)]
    [∀ i, Algebra.FinitePresentation R (T i)] :
    Algebra.FinitePresentation R A :=
  Algebra.FinitePresentation.of_span_eq_top_target_of_isLocalizationAway s hs T

/-- The fixed-point affine-local finite presentation theorem.

Here T i is the fixed-point algebra of the localized B-algebra at s i.
FixedLocalizationAction.awayFixedPointsEquiv constructs the localization
equivalence A_[s i] to (B_[s i])^G; this theorem consumes its local
IsLocalization and finite-presentation consequences. -/
theorem fixedPoints_affineLocal_finitePresentation
    [Fintype G] [Algebra.IsInvariant A B G]
    {ι : Type*} [Finite ι] (s : ι → A)
    (hs : Ideal.span (Set.range s) = ⊤)
    [∀ i, Algebra R (FixedPoints.subring
      (AwayLocalization (B := B) (s i)) G)]
    [∀ i, Algebra A (FixedPoints.subring
      (AwayLocalization (B := B) (s i)) G)]
    [∀ i, IsScalarTower R A (FixedPoints.subring
      (AwayLocalization (B := B) (s i)) G)]
    [∀ i, IsLocalization.Away (s i) (FixedPoints.subring
      (AwayLocalization (B := B) (s i)) G)]
    [∀ i, Algebra.FinitePresentation R (FixedPoints.subring
      (AwayLocalization (B := B) (s i)) G)] :
    Algebra.FinitePresentation R A :=
  affineLocal_finitePresentation s hs
    (fun i => FixedPoints.subring (AwayLocalization (B := B) (s i)) G)

/-- The localization descent identity supplied by FixedLocalizationAction:
for finite G and invariant base A, the fixed points of B_f are the
localized invariant ring. -/
noncomputable def fixedPoints_localization_equiv
    [Fintype G] [Algebra.IsInvariant A B G]
    (hinj : Function.Injective (algebraMap A B)) (f : A) :
    RingEquiv (Localization.Away f) (FixedPoints.subring
      (AwayLocalization (B := B) f) G) :=
  awayFixedPointsEquiv (B := B) (G := G) f hinj

end

end ABCBridge.InvariantsFinitePresentationGeneral
