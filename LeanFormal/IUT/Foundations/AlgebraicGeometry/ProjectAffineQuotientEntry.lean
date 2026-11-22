import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof

/-!
# Project-facing affine quotient entry

Consumer of the actual affine finite-etale quotient Spec (Gamma(X)^G): the
projection, its invariance, the affine universal property, the factor map and
its uniqueness, and the affine cover carrier. No quotient or factorization is
fabricated.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof

namespace LeanFormal.IUT.ProjectAffineQuotientEntry

universe u

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G]

/-- Project-facing affine quotient data. -/
noncomputable def projectAffineQuotientData
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] :
    AffineFiniteEtaleQuotient (R := R) (G := G) A :=
  affineFiniteEtaleQuotient (R := R) (G := G) A

/-- The quotient scheme is the spectrum of fixed points. -/
theorem projectAffineQuotientScheme_eq
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] :
    affineQuotientScheme (R := R) (G := G) A =
      Spec (CommRingCat.of (FixedPoints.subalgebra R A G)) :=
  affineQuotientScheme_eq (R := R) (G := G) A

/-- The projection is invariant. -/
theorem projectAffineQuotientProjection_invariant
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A] (g : G) :
    specAction (R := R) (G := G) (A := A) g ≫
        (projectAffineQuotientData (R := R) (G := G) A).projection =
      (projectAffineQuotientData (R := R) (G := G) A).projection :=
  (projectAffineQuotientData (R := R) (G := G) A).invariant g

/-- The actual affine-target universal property. -/
theorem projectAffineQuotientUniversal
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) :
    ∃! u : affineQuotientScheme (R := R) (G := G) A ⟶
        Spec (CommRingCat.of B),
      (projectAffineQuotientData (R := R) (G := G) A).projection ≫ u = f :=
  (projectAffineQuotientData (R := R) (G := G) A).universal B f hf

/-- The factor map and its uniqueness. -/
theorem projectAffineQuotientFactor_spec
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) :
    (projectAffineQuotientData (R := R) (G := G) A).projection ≫
        affineFiniteEtaleQuotientFactor (R := R) (G := G) (A := A) B f hf = f ∧
      (∀ u : affineQuotientScheme (R := R) (G := G) A ⟶
          Spec (CommRingCat.of B),
        (projectAffineQuotientData (R := R) (G := G) A).projection ≫ u = f →
          u = affineFiniteEtaleQuotientFactor (R := R) (G := G) (A := A) B f hf) :=
  ⟨affineFiniteEtaleQuotientFactor_fac (R := R) (G := G) (A := A) B f hf,
    fun u hu =>
      affineFiniteEtaleQuotientFactor_uniq (R := R) (G := G) (A := A) B f hf u hu⟩

/-- Affine finite-etale cover carrier consumer. -/
theorem projectAffineQuotientCoverEntry
    (X : LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations.FiniteEtaleCover
      (Spec (CommRingCat.of R)))
    (A : Type u) [CommRing A] [Algebra R A]
    [MulSemiringAction G A] [SMulCommClass G R A]
    (B : Type u) [CommRing B]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of B))
    (hf : ∀ g : G, specAction (R := R) (G := G) (A := A) g ≫ f = f) :
    IsAffine X.carrier ∧
      (Nonempty (X.carrier ≅ Spec Γ(X.carrier, ⊤))) ∧
      (∃! u : affineQuotientScheme (R := R) (G := G) A ⟶
          Spec (CommRingCat.of B),
        (projectAffineQuotientData (R := R) (G := G) A).projection ≫ u = f) :=
  affineFiniteEtaleQuotient_cover_consumer (R := R) (G := G) X A B f hf

end LeanFormal.IUT.ProjectAffineQuotientEntry
end
