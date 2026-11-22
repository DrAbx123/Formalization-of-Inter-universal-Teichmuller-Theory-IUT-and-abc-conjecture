import LeanFormal.IUT.Foundations.AlgebraicGeometry.ProjectAffineQuotientEntry
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineFiniteEtaleQuotientConsumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientMapFinite
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.ProjectAffineQuotientCoverEntry

universe u

open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientCoverProjection
open LeanFormal.IUT.Foundations.AlgebraicGeometry.QuotientMapFinite
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [Finite G]

variable (X : FiniteEtaleCover (Spec (CommRingCat.of R)))
variable [Algebra R Γ(X.carrier, ⊤)]
variable [MulSemiringAction G Γ(X.carrier, ⊤)]
variable [SMulCommClass G R Γ(X.carrier, ⊤)]
variable [Module.Finite R Γ(X.carrier, ⊤)]

abbrev coverSections : Type u := Γ(X.carrier, ⊤)

abbrev coverQuotientScheme : Scheme.{u} := affineQuotientScheme (R := R) (G := G) (coverSections X)

noncomputable def coverQuotientProjection : X.carrier ⟶ coverQuotientScheme (R := R) (G := G) X :=
  quotientProjection (R := R) (G := G) (X := X.carrier)

theorem coverQuotientProjection_isFinite : IsFinite (coverQuotientProjection (R := R) (G := G) X) :=
  quotientProjection_isFinite (R := R) (G := G) (X := X.carrier)

theorem coverQuotientProjection_over
    (hiso : X.carrier.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (coverSections X))) = X.structureMap) :
    coverQuotientProjection (R := R) (G := G) X ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R (fixedPointSubalgebra R (coverSections X) G))) = X.structureMap :=
  quotientProjection_over_spec (R := R) (G := G) (X := X.carrier) X.structureMap hiso


/-- Compatibility data for a scheme-level action on the cover whose induced
morphisms fix the quotient projection.  This is the conditional action interface
used by the Project-facing entry. -/
structure CoverActionCompatibility where
  act : G → (X.carrier ⟶ X.carrier)
  invariant : ∀ g : G,
    act g ≫ coverQuotientProjection (R := R) (G := G) X =
      coverQuotientProjection (R := R) (G := G) X

/-- Project-facing cover entry: finite and over-Spec-R projection, the
G-invariance supplied by the action interface, and the affine quotient
universal property. -/
theorem projectAffineQuotientCoverEntry
    (hiso : X.carrier.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (coverSections X))) = X.structureMap)
    (D : CoverActionCompatibility (R := R) (G := G) X) :
    IsFinite (coverQuotientProjection (R := R) (G := G) X) ∧
      (coverQuotientProjection (R := R) (G := G) X ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R (fixedPointSubalgebra R (coverSections X) G))) = X.structureMap) ∧
      (∀ g : G,
        D.act g ≫ coverQuotientProjection (R := R) (G := G) X =
          coverQuotientProjection (R := R) (G := G) X) ∧
      (∀ (B : Type u) [CommRing B]
        (f : Spec (CommRingCat.of (coverSections X)) ⟶ Spec (CommRingCat.of B)),
        (∀ g : G,
          specAction (R := R) (G := G) (A := coverSections X) g ≫ f = f) →
          ∃! u : affineQuotientScheme (R := R) (G := G) (coverSections X) ⟶
            Spec (CommRingCat.of B),
            affineQuotientProjection (R := R) (G := G) (coverSections X) ≫ u = f) :=
  ⟨coverQuotientProjection_isFinite (R := R) (G := G) X,
    coverQuotientProjection_over (R := R) (G := G) X hiso,
    D.invariant,
    fun B _ f hf =>
      affineQuotientUniversal (R := R) (G := G) (A := coverSections X) B f hf⟩
end LeanFormal.IUT.Foundations.AlgebraicGeometry.ProjectAffineQuotientCoverEntry
