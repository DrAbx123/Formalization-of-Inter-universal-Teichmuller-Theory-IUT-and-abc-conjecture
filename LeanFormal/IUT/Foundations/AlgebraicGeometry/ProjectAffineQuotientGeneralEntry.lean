import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientActionDataFromCover

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open _root_.LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration
open _root_.LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof
open _root_.ABCBridge.CoverSectionsAction
open _root_.ABCBridge.AffineQuotientActionDataFromCover

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.ProjectAffineQuotientGeneralEntry

universe u

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G]
variable (X : FiniteEtaleCover (Spec (CommRingCat.of R)))
variable (act : G →* CategoryTheory.Aut X)

/-- The coordinate ring of the cover. -/
abbrev coverSections : Type u := Γ(X.carrier, ⊤)

/-- The actual quotient scheme Spec(A^G). -/
abbrev coverQuotientScheme : Scheme.{u} :=
  actualQuotientScheme X act

/-- The quotient projection on the original carrier. -/
noncomputable def coverQuotientProjection :
    X.carrier ⟶ coverQuotientScheme (R := R) (G := G) X act :=
  actualCarrierProjection X act

/-- The quotient projection on the coordinate Spectrum. -/
noncomputable def coverCoordinateProjection :
    Spec (CommRingCat.of (coverSections X)) ⟶
      coverQuotientScheme (R := R) (G := G) X act :=
  actualCoordinateProjection X act

/-- The carrier projection factors through isoSpec and the coordinate projection. -/
theorem coverQuotientProjection_eq_isoSpec :
    coverQuotientProjection (R := R) (G := G) X act =
      X.carrier.isoSpec.hom ≫
        coverCoordinateProjection (R := R) (G := G) X act :=
  actualCarrierProjection_eq X act

/-- The quotient projection is the package projection. -/
theorem coverCoordinateProjection_eq_package :
    letI := coverAction X act
    letI := coverActionComm X act
    (actualAffineFiniteEtaleQuotient X act).projection =
      coverCoordinateProjection (R := R) (G := G) X act :=
  actualAffineFiniteEtaleQuotient_projection X act

/-- Invariance of the quotient projection under the transported action. -/
theorem coverQuotientProjection_invariant (g : G) :
    letI := coverAction X act
    letI := coverActionComm X act
    specAction (R := R) (G := G) (A := coverSections X) g ≫
        coverCoordinateProjection (R := R) (G := G) X act =
      coverCoordinateProjection (R := R) (G := G) X act :=
  actualCoordinateProjection_invariant X act g

/-- The affine universal property for the actual cover quotient. -/
theorem coverQuotientProjection_universal
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of (coverSections X)) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G,
      letI := coverAction X act
      letI := coverActionComm X act
      specAction (R := R) (G := G) (A := coverSections X) g ≫ f = f) :
    ∃! v : coverQuotientScheme (R := R) (G := G) X act ⟶
        Spec (CommRingCat.of B),
      coverCoordinateProjection (R := R) (G := G) X act ≫ v = f :=
  actualCoordinateProjection_universal X act B f hf

/-- Project entry: coordinate algebra, quotient scheme, projection
factorization, invariance, and the affine universal property for an arbitrary
finite etale cover with a cover action. -/
theorem projectAffineQuotientGeneralEntry
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of (coverSections X)) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G,
      letI := coverAction X act
      letI := coverActionComm X act
      specAction (R := R) (G := G) (A := coverSections X) g ≫ f = f) :
    (coverQuotientProjection (R := R) (G := G) X act =
        X.carrier.isoSpec.hom ≫
          coverCoordinateProjection (R := R) (G := G) X act) ∧
      (letI := coverAction X act
       letI := coverActionComm X act
       (actualAffineFiniteEtaleQuotient X act).projection =
         coverCoordinateProjection (R := R) (G := G) X act) ∧
      (∀ g : G,
        letI := coverAction X act
        letI := coverActionComm X act
        specAction (R := R) (G := G) (A := coverSections X) g ≫
            coverCoordinateProjection (R := R) (G := G) X act =
          coverCoordinateProjection (R := R) (G := G) X act) ∧
      (∃! v : coverQuotientScheme (R := R) (G := G) X act ⟶
          Spec (CommRingCat.of B),
        coverCoordinateProjection (R := R) (G := G) X act ≫ v = f) :=
  ⟨coverQuotientProjection_eq_isoSpec (R := R) (G := G) X act,
    coverCoordinateProjection_eq_package (R := R) (G := G) X act,
    fun g => coverQuotientProjection_invariant (R := R) (G := G) X act g,
    coverQuotientProjection_universal (R := R) (G := G) X act B f hf⟩

end LeanFormal.IUT.Foundations.AlgebraicGeometry.ProjectAffineQuotientGeneralEntry
