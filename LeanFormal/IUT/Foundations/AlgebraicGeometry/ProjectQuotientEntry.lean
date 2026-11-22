import LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientUniversalPropertyIntegration
import LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientUniversalProperty

/-!
# Project quotient entry consumer

The first production project-entry consumer of the 0.3 quotient universal
property.  It combines the actual affine-target universal property with the
actual global glued quotient descent (restriction, factorization, uniqueness).
No residual variant and no ProjectL0-only aggregate is introduced.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof
open _root_.LeanFormal.IUT.Foundations.AlgebraicGeometry.GlobalQuotientUniversalProperty
open _root_.LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientUniversalPropertyIntegration

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.ProjectQuotientEntry

universe u

/-- Project-entry consumer of the quotient universal property: affine-target
universality together with global glued desc, its chart factorization, and its
uniqueness. -/
theorem quotientEntryConsumer
    {R : Type u} [CommRing R]
    {G : Type u} [Group G] [Fintype G]
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    {S : Scheme.{u}} (D : GlobalGluedQuotientData S)
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f)
    (Z : Scheme.{u}) (F : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hF : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ F i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ F j) :
    (∃! u : Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶
        Spec (CommRingCat.of B),
      affineQuotientMap (R := R) (G := G) (A := A) ≫ u = f) ∧
      (∀ i : D.P.J,
        (D.P.toSchemeGlueData).ι i ≫ D.desc Z F hF = F i) ∧
      (∀ u : D.cover.carrier ⟶ Z,
        (∀ i : D.P.J, (D.P.toSchemeGlueData).ι i ≫ u = F i) →
          u = D.desc Z F hF) :=
  ⟨affineTargetUniversal_consumer (R := R) (G := G) (A := A) B f hf,
    (globalGluedQuotient_universal_consumer D Z F hF).1,
    (globalGluedQuotient_universal_consumer D Z F hF).2⟩

/-- The affine-target component alone, exposed for downstream project users. -/
theorem quotientEntryConsumer_affine
    {R : Type u} [CommRing R]
    {G : Type u} [Group G]
    {A : Type u} [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) :
    ∃! u : Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) ⟶
        Spec (CommRingCat.of B),
      affineQuotientMap (R := R) (G := G) (A := A) ≫ u = f :=
  affineTargetUniversal_consumer (R := R) (G := G) (A := A) B f hf

/-- The global glued-desc component alone, exposed for downstream project users. -/
theorem quotientEntryConsumer_glued
    {S : Scheme.{u}} (D : GlobalGluedQuotientData S)
    (Z : Scheme.{u}) (F : ∀ i : D.P.J, D.P.U i ⟶ Z)
    (hF : ∀ i j : D.P.J,
      pullback.fst ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ F i =
        pullback.snd ((D.P.toSchemeGlueData).ι i) ((D.P.toSchemeGlueData).ι j) ≫ F j) :
    (∀ i : D.P.J,
        (D.P.toSchemeGlueData).ι i ≫ D.desc Z F hF = F i) ∧
      (∀ u : D.cover.carrier ⟶ Z,
        (∀ i : D.P.J, (D.P.toSchemeGlueData).ι i ≫ u = F i) →
          u = D.desc Z F hF) :=
  globalGluedQuotient_universal_consumer D Z F hF

end LeanFormal.IUT.Foundations.AlgebraicGeometry.ProjectQuotientEntry
