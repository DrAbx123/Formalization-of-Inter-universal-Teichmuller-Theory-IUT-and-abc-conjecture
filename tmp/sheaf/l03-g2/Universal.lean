import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration
import LeanFormal.IUT.Foundations.AlgebraicGeometry.CoverSectionsAction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

namespace SHEAF.L03.Universal

universe u

open ABCBridge.CoverSectionsAction
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientIntegration
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineOverlapQuotientTransportProof
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [Finite G]
variable (X : FiniteEtaleCover (Spec (CommRingCat.of R)))
variable (act : G →* CategoryTheory.Aut X)

local instance sectionsAlgebra : Algebra R (CoverSections X) :=
  coverSectionsAlgebra X

local instance sectionsAction : MulSemiringAction G (CoverSections X) :=
  coverSectionsMulSemiringAction X act

local instance sectionsComm : SMulCommClass G R (CoverSections X) :=
  coverSectionsSMulCommClass X act

/-- Underlying scheme map of a cover morphism. -/
noncomputable def coverLeft {Z : FiniteEtaleCover (Spec (CommRingCat.of R))} (f : X ⟶ Z) :
    X.carrier ⟶ Z.carrier :=
  (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map f).left

/-- Underlying scheme automorphism of the cover action at g. -/
noncomputable def actLeft (g : G) : X.carrier ⟶ X.carrier :=
  (FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R)) |>.map (act g).hom).left

/-- The fixed-point quotient scheme. -/
abbrev Q : Scheme.{u} :=
  Spec (CommRingCat.of (FixedPoints.subalgebra R (CoverSections X) G))

/-- The quotient projection. -/
noncomputable def pi : X.carrier ⟶ Q := by
  haveI : IsAffine X.carrier := finiteEtaleCoverCarrier_affine X
  letI : Algebra R (CoverSections X) := coverSectionsAlgebra X
  letI : MulSemiringAction G (CoverSections X) := coverSectionsMulSemiringAction X act
  letI : SMulCommClass G R (CoverSections X) := coverSectionsSMulCommClass X act
  exact X.carrier.isoSpec.hom ≫ affineQuotientProjection (R := R) (G := G) (A := CoverSections X)

/-- The quotient projection is invariant under the cover action. -/
theorem pi_invariant (g : G) :
    actLeft X act g ≫ pi X act = pi X act := by
  haveI : IsAffine X.carrier := finiteEtaleCoverCarrier_affine X
  letI : Algebra R (CoverSections X) := coverSectionsAlgebra X
  letI : MulSemiringAction G (CoverSections X) := coverSectionsMulSemiringAction X act
  letI : SMulCommClass G R (CoverSections X) := coverSectionsSMulCommClass X act
  unfold pi
  rw [← Category.assoc, coverSectionsSpecAut_agrees X act g]
  congr 1
  have hspec : coverSectionsSpecAut X act g =
      specAction (R := R) (G := G) (A := CoverSections X) (g⁻¹) := rfl
  rw [hspec]
  exact affineQuotientProjection_invariant (R := R) (G := G) (A := CoverSections X) (g := g⁻¹)

/-- The affine map attached to a cover morphism. -/
noncomputable def targetAffine (Z : FiniteEtaleCover (Spec (CommRingCat.of R)))
    (f : X ⟶ Z) :
    Spec (CommRingCat.of (CoverSections X)) ⟶ Spec (CommRingCat.of (CoverSections Z)) := by
  haveI : IsAffine X.carrier := finiteEtaleCoverCarrier_affine X
  haveI : IsAffine Z.carrier := finiteEtaleCoverCarrier_affine Z
  exact X.carrier.isoSpec.inv ≫ coverLeft X f ≫ Z.carrier.isoSpec.hom

/-- Invariance of the affine map for a G-invariant cover morphism. -/
theorem targetAffine_invariant (Z : FiniteEtaleCover (Spec (CommRingCat.of R)))
    (f : X ⟶ Z) (hf : ∀ g : G, actLeft X act g ≫ coverLeft X f = coverLeft X f) (g : G) :
    specAction (R := R) (G := G) (A := CoverSections X) g ≫
        targetAffine X Z f = targetAffine X Z f := by
  haveI : IsAffine X.carrier := finiteEtaleCoverCarrier_affine X
  haveI : IsAffine Z.carrier := finiteEtaleCoverCarrier_affine Z
  letI : Algebra R (CoverSections X) := coverSectionsAlgebra X
  letI : MulSemiringAction G (CoverSections X) := coverSectionsMulSemiringAction X act
  letI : SMulCommClass G R (CoverSections X) := coverSectionsSMulCommClass X act
  unfold targetAffine
  have hspec : specAction (R := R) (G := G) (A := CoverSections X) g =
      X.carrier.isoSpec.inv ≫ actLeft X act g⁻¹ ≫ X.carrier.isoSpec.hom := rfl
  rw [hspec]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc]
  rw [hf g⁻¹]

/-- Universal property of the quotient projection for G-invariant cover morphisms. -/
theorem universal (Z : FiniteEtaleCover (Spec (CommRingCat.of R)))
    (f : X ⟶ Z) (hf : ∀ g : G, actLeft X act g ≫ coverLeft X f = coverLeft X f) :
    ∃! u : Q ⟶ Z.carrier,
      pi X act ≫ u = coverLeft X f := by
  haveI : IsAffine X.carrier := finiteEtaleCoverCarrier_affine X
  haveI : IsAffine Z.carrier := finiteEtaleCoverCarrier_affine Z
  letI : Algebra R (CoverSections X) := coverSectionsAlgebra X
  letI : MulSemiringAction G (CoverSections X) := coverSectionsMulSemiringAction X act
  letI : SMulCommClass G R (CoverSections X) := coverSectionsSMulCommClass X act
  let B := CoverSections Z
  let target := targetAffine X Z f
  have htarget : ∀ g : G,
      specAction (R := R) (G := G) (A := CoverSections X) g ≫ target = target :=
    targetAffine_invariant X act Z f hf
  obtain ⟨u, hu, huniq⟩ :=
    affineQuotientUniversal (R := R) (G := G) (A := CoverSections X) B target htarget
  refine ⟨u ≫ Z.carrier.isoSpec.inv, ?_, ?_⟩
  · unfold pi
    rw [Category.assoc]
    rw [hu]
    unfold target targetAffine
    simp only [Category.assoc]
    rw [Iso.hom_inv_id_assoc]
    rw [Iso.inv_hom_id_assoc]
  · intro v hv
    have hv' : affineQuotientProjection (R := R) (G := G) (A := CoverSections X) ≫
        (v ≫ Z.carrier.isoSpec.hom) = target := by
      unfold pi at hv
      unfold target targetAffine
      rw [← hv]
      simp only [Category.assoc]
      rw [Iso.hom_inv_id_assoc]
      rw [Iso.inv_hom_id_assoc]
    have hvu := huniq (v ≫ Z.carrier.isoSpec.hom) hv'
    rw [hvu]
    simp only [Category.assoc]
    rw [Iso.inv_hom_id_assoc]

end SHEAF.L03.Universal
