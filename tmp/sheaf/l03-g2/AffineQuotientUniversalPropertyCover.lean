import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration
import LeanFormal.IUT.Foundations.AlgebraicGeometry.CoverSectionsAction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ABCBridge.AffineQuotientUniversalPropertyCover

universe u

open ABCBridge.CoverSectionsAction
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

attribute [local instance] LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration.finiteEtaleCoverCarrier_affine

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [Finite G]
variable {X : FiniteEtaleCover (Spec (CommRingCat.of R))}
variable (act : G →* CategoryTheory.Aut X)

local instance sectionsAlgebra : Algebra R (CoverSections X) :=
  coverSectionsAlgebra X

local instance sectionsAction : MulSemiringAction G (CoverSections X) :=
  coverSectionsMulSemiringAction X act

local instance sectionsComm : SMulCommClass G R (CoverSections X) :=
  coverSectionsSMulCommClass X act

/-- The fixed-point quotient scheme of the coordinate algebra. -/
abbrev quotientScheme : Scheme.{u} :=
  affineQuotientScheme (R := R) (G := G) (A := CoverSections X)

/-- The actual quotient projection X -> Spec(Gamma(X)^G). -/
noncomputable def quotientProjection : X.carrier ⟶ quotientScheme (R := R) (G := G) (X := X) (act := act) :=
  X.carrier.isoSpec.hom ≫
    affineQuotientProjection (R := R) (G := G) (A := CoverSections X)

/-- The quotient projection is invariant under the cover action. -/
theorem quotientProjection_invariant (g : G) :
    (act g).hom ≫ quotientProjection (R := R) (G := G) (X := X) act =
      quotientProjection (R := R) (G := G) (X := X) act := by
  unfold quotientProjection
  rw [← Category.assoc, coverSectionsSpecAut_agrees X act g]
  congr 1
  -- the spec action induced by the section action is the inverse section automorphism
  change coverSectionsSpecAut X act g ≫
      affineQuotientProjection (R := R) (G := G) (A := CoverSections X) = _
  have h := affineQuotientProjection_invariant (R := R) (G := G)
    (A := CoverSections X) (g := g⁻¹)
  -- identify coverSectionsSpecAut g with specAction g⁻¹
  convert h using 2
  · rfl

/-- The affine map associated to a cover morphism X -> Z. -/
noncomputable def targetAffineMap (Z : FiniteEtaleCover (Spec (CommRingCat.of R)))
    (f : X ⟶ Z) :
    Spec (CommRingCat.of (CoverSections X)) ⟶
      Spec (CommRingCat.of (CoverSections Z)) :=
  X.carrier.isoSpec.inv ≫ f.left ≫ Z.carrier.isoSpec.hom

/-- The affine map is invariant when the cover morphism is G-invariant. -/
theorem targetAffineMap_invariant (Z : FiniteEtaleCover (Spec (CommRingCat.of R)))
    (f : X ⟶ Z) (hf : ∀ g : G, (act g).hom ≫ f.left = f.left) (g : G) :
    specAction (R := R) (G := G) (A := CoverSections X) g ≫
        targetAffineMap (R := R) (G := G) (X := X) Z f =
      targetAffineMap (R := R) (G := G) (X := X) Z f := by
  unfold targetAffineMap
  -- specAction is the inverse section automorphism; rewrite via isoSpec coherence
  have hspec : specAction (R := R) (G := G) (A := CoverSections X) g =
      X.carrier.isoSpec.inv ≫ coverAutSchemeIso X act g⁻¹ ≫ X.carrier.isoSpec.hom := by
    rfl
  rw [hspec]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc, hf g⁻¹]

/-- Universal property: every G-invariant cover morphism factors uniquely through
the quotient projection. -/
theorem quotientUniversal (Z : FiniteEtaleCover (Spec (CommRingCat.of R)))
    (f : X ⟶ Z) (hf : ∀ g : G, (act g).hom ≫ f.left = f.left) :
    ∃! u : quotientScheme (R := R) (G := G) (X := X) (act := act) ⟶ Z.carrier,
      quotientProjection (R := R) (G := G) (X := X) act ≫ u = f.left := by
  let B := CoverSections Z
  let target := targetAffineMap (R := R) (G := G) (X := X) Z f
  have htarget : ∀ g : G,
      specAction (R := R) (G := G) (A := CoverSections X) g ≫ target = target :=
    targetAffineMap_invariant (R := R) (G := G) (X := X) act Z f hf
  obtain ⟨u, hu, huniq⟩ :=
    affineQuotientUniversal (R := R) (G := G) (A := CoverSections X) B target htarget
  refine ⟨u ≫ Z.carrier.isoSpec.inv, ?_, ?_⟩
  · -- fac
    unfold quotientProjection
    rw [Category.assoc]
    rw [hu]
    unfold target
    simp only [targetAffineMap, Category.assoc]
    rw [Iso.hom_inv_id_assoc]
    rw [Iso.inv_hom_id_assoc]
  · intro v hv
    -- uniqueness
    have hv' : affineQuotientProjection (R := R) (G := G) (A := CoverSections X) ≫
        (v ≫ Z.carrier.isoSpec.hom) = target := by
      unfold quotientProjection at hv
      unfold target targetAffineMap
      rw [← hv]
      simp only [Category.assoc]
      rw [Iso.hom_inv_id_assoc]
      rw [Iso.hom_inv_id_assoc]
    have hvu := huniq (v ≫ Z.carrier.isoSpec.hom) hv'
    rw [hvu]
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_assoc]

end ABCBridge.AffineQuotientUniversalPropertyCover
