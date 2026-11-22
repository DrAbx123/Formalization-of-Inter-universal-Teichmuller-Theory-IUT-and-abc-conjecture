import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientGluedCover
import LeanFormal.IUT.Foundations.AlgebraicGeometry.RegularPermutationQuotientConsumer
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations

/-!
# Affine finite-etale quotient integration

For an affine finite-etale cover with coordinate algebra A = Γ(X), the actual
quotient is Q = Spec (A^G) with projection X → Q induced by the fixed-point
inclusion.  This file assembles the actual affine-target universal property for
G-invariant cover morphisms and packages the final quotient consumer.  The
finite-etale cover carrier affineness is consumed from the production cover
module.  No residual-only variant and no fabricated quotient are introduced.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof
open _root_.LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open _root_.LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration

universe u

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G]

/-- The fixed-point algebra of the coordinate ring. -/
abbrev affineQuotientAlgebra
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] : Type u :=
  FixedPoints.subalgebra R A G

/-- The actual affine quotient scheme Spec (A^G). -/
noncomputable abbrev affineQuotientScheme
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] : Scheme.{u} :=
  Spec (CommRingCat.of (affineQuotientAlgebra (R := R) (G := G) A))

/-- The actual projection Spec A → Spec (A^G). -/
noncomputable def affineQuotientProjection
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] :
    Spec (CommRingCat.of A) ⟶ affineQuotientScheme (R := R) (G := G) A :=
  affineQuotientMap (R := R) (G := G) (A := A)

/-- The projection is invariant under the transported action. -/
theorem affineQuotientProjection_invariant
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (g : G) :
    specAction (R := R) (G := G) (A := A) g ≫
        affineQuotientProjection (R := R) (G := G) A =
      affineQuotientProjection (R := R) (G := G) A :=
  affineQuotientMap_invariant (R := R) (G := G) (A := A) g

/-- The affine-target universal property for G-invariant cover morphisms:
every invariant morphism to an affine target factors uniquely through the
actual projection. -/
theorem affineQuotientUniversal
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) :
    ∃! u : affineQuotientScheme (R := R) (G := G) A ⟶
        Spec (CommRingCat.of B),
      affineQuotientProjection (R := R) (G := G) A ≫ u = f :=
  affineTargetUniversal (R := R) (G := G) (A := A) B f hf

/-- The factorization map provided by the affine quotient universal property. -/
noncomputable def affineQuotientFactor
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) :
    affineQuotientScheme (R := R) (G := G) A ⟶
      Spec (CommRingCat.of B) :=
  (affineQuotientUniversal (R := R) (G := G) (A := A) B f hf).choose

theorem affineQuotientFactor_fac
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) :
    affineQuotientProjection (R := R) (G := G) A ≫
        affineQuotientFactor (R := R) (G := G) (A := A) B f hf = f :=
  (affineQuotientUniversal (R := R) (G := G) (A := A) B f hf).choose_spec.1

theorem affineQuotientFactor_uniq
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f)
    (u : affineQuotientScheme (R := R) (G := G) A ⟶
      Spec (CommRingCat.of B))
    (hu : affineQuotientProjection (R := R) (G := G) A ≫ u = f) :
    u = affineQuotientFactor (R := R) (G := G) (A := A) B f hf :=
  (affineQuotientUniversal (R := R) (G := G) (A := A) B f hf).choose_spec.2 u hu

/-! ## Affine finite-etale cover carrier -/

/-- The carrier of a finite-etale cover over an affine base is affine. -/
theorem finiteEtaleCoverCarrier_affine
    (X : FiniteEtaleCover (Spec (CommRingCat.of R))) :
    IsAffine X.carrier :=
  finiteEtaleCoverCarrier_isAffine R X

/-- The canonical coordinate isomorphism X ≅ Spec Γ(X) for the affine carrier
of a finite-etale cover. -/
noncomputable def finiteEtaleCoverCoordinateIso
    (X : FiniteEtaleCover (Spec (CommRingCat.of R))) :
    X.carrier ≅ Spec Γ(X.carrier, ⊤) :=
  Scheme.isoSpec X.carrier

theorem finiteEtaleCoverCoordinateIso_hom
    (X : FiniteEtaleCover (Spec (CommRingCat.of R))) :
    (finiteEtaleCoverCoordinateIso X).hom = X.carrier.toSpecΓ :=
  Scheme.isoSpec_hom X.carrier

/-! ## Final consumer package -/

/-- The actual affine finite-etale quotient data: coordinate algebra, quotient
scheme, projection, invariance, and the affine-target universal property. -/
structure AffineFiniteEtaleQuotient
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] where
  projection : Spec (CommRingCat.of A) ⟶
    affineQuotientScheme (R := R) (G := G) A
  projection_eq : projection = affineQuotientProjection (R := R) (G := G) A
  invariant : ∀ g : G,
    specAction (R := R) (G := G) (A := A) g ≫ projection = projection
  universal : ∀ (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B)),
    (∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) →
      ∃! u : affineQuotientScheme (R := R) (G := G) A ⟶
        Spec (CommRingCat.of B), projection ≫ u = f

/-- The actual affine finite-etale quotient package. -/
noncomputable def affineFiniteEtaleQuotient
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] :
    AffineFiniteEtaleQuotient (R := R) (G := G) A where
  projection := affineQuotientProjection (R := R) (G := G) A
  projection_eq := rfl
  invariant := affineQuotientProjection_invariant (R := R) (G := G) A
  universal := fun B _ f hf =>
    affineQuotientUniversal (R := R) (G := G) (A := A) B f hf

theorem affineFiniteEtaleQuotient_quotient
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] :
    affineQuotientScheme (R := R) (G := G) A =
      affineQuotientScheme (R := R) (G := G) A :=
  rfl

theorem affineFiniteEtaleQuotient_projection
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] :
    (affineFiniteEtaleQuotient (R := R) (G := G) A).projection =
      affineQuotientProjection (R := R) (G := G) A :=
  rfl

/-- The final consumer theorem: the actual affine finite-etale quotient has the
expected projection and universal property. -/
theorem affineFiniteEtaleQuotient_consumer
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) :
    ∃! u : affineQuotientScheme (R := R) (G := G) A ⟶
        Spec (CommRingCat.of B),
      (affineFiniteEtaleQuotient (R := R) (G := G) A).projection ≫ u = f :=
  (affineFiniteEtaleQuotient (R := R) (G := G) A).universal B f hf

/-- Combined consumer: affine cover carrier, coordinate isomorphism, quotient
projection, and affine universal property. -/
theorem affineFiniteEtaleQuotient_cover_consumer
    (X : FiniteEtaleCover (Spec (CommRingCat.of R)))
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) :
    IsAffine X.carrier ∧
      (Nonempty (X.carrier ≅ Spec Γ(X.carrier, ⊤))) ∧
      (∃! u : affineQuotientScheme (R := R) (G := G) A ⟶
          Spec (CommRingCat.of B),
        (affineFiniteEtaleQuotient (R := R) (G := G) A).projection ≫ u = f) :=
  ⟨finiteEtaleCoverCarrier_affine X,
    ⟨finiteEtaleCoverCoordinateIso (R := R) X⟩,
    affineFiniteEtaleQuotient_consumer (R := R) (G := G) (A := A) B f hf⟩

theorem affineQuotientProjection_eq
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] :
    affineQuotientProjection (R := R) (G := G) A =
      affineQuotientMap (R := R) (G := G) (A := A) :=
  rfl

theorem affineQuotientScheme_eq
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] :
    affineQuotientScheme (R := R) (G := G) A =
      Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) :=
  rfl

theorem affineFiniteEtaleQuotient_projection_invariant
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (g : G) :
    specAction (R := R) (G := G) (A := A) g ≫
        (affineFiniteEtaleQuotient (R := R) (G := G) A).projection =
      (affineFiniteEtaleQuotient (R := R) (G := G) A).projection :=
  (affineFiniteEtaleQuotient (R := R) (G := G) A).invariant g

theorem affineFiniteEtaleQuotient_universal
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) :
    ∃! u : affineQuotientScheme (R := R) (G := G) A ⟶
        Spec (CommRingCat.of B),
      (affineFiniteEtaleQuotient (R := R) (G := G) A).projection ≫ u = f :=
  (affineFiniteEtaleQuotient (R := R) (G := G) A).universal B f hf

noncomputable def affineFiniteEtaleQuotientFactor
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) :
    affineQuotientScheme (R := R) (G := G) A ⟶
      Spec (CommRingCat.of B) :=
  (affineFiniteEtaleQuotient (R := R) (G := G) A).universal B f hf |>.choose

theorem affineFiniteEtaleQuotientFactor_fac
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) :
    (affineFiniteEtaleQuotient (R := R) (G := G) A).projection ≫
        affineFiniteEtaleQuotientFactor (R := R) (G := G) (A := A) B f hf = f :=
  (affineFiniteEtaleQuotient (R := R) (G := G) A).universal B f hf |>.choose_spec.1

theorem affineFiniteEtaleQuotientFactor_uniq
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f)
    (u : affineQuotientScheme (R := R) (G := G) A ⟶
      Spec (CommRingCat.of B))
    (hu : (affineFiniteEtaleQuotient (R := R) (G := G) A).projection ≫ u = f) :
    u = affineFiniteEtaleQuotientFactor (R := R) (G := G) (A := A) B f hf :=
  (affineFiniteEtaleQuotient (R := R) (G := G) A).universal B f hf |>.choose_spec.2 u hu

theorem finiteEtaleCoverCoordinateIso_inv
    (X : FiniteEtaleCover (Spec (CommRingCat.of R))) :
    (finiteEtaleCoverCoordinateIso (R := R) X).inv ≫ X.carrier.toSpecΓ =
      𝟙 (Spec Γ(X.carrier, ⊤)) :=
  Scheme.isoSpec_inv_toSpecΓ X.carrier

theorem finiteEtaleCoverCoordinateIso_hom_inv
    (X : FiniteEtaleCover (Spec (CommRingCat.of R))) :
    (finiteEtaleCoverCoordinateIso (R := R) X).hom ≫
        (finiteEtaleCoverCoordinateIso (R := R) X).inv = 𝟙 X.carrier :=
  (finiteEtaleCoverCoordinateIso (R := R) X).hom_inv_id

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration
