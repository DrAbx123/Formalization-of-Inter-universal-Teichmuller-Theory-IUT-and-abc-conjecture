import LeanFormal.IUT.Foundations.AlgebraicGeometry.CoverSectionsAction
import LeanFormal.IUT.Foundations.AlgebraicGeometry.ProjectAffineQuotientCoverEntry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.CoverActionCompatibilityFromSections

universe u

open ABCBridge.CoverSectionsAction
open LeanFormal.IUT.Foundations.AlgebraicGeometry.ProjectAffineQuotientCoverEntry
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

variable {R : Type u} [CommRing R]
variable {G : Type u} [Group G] [Finite G]
variable (X : FiniteEtaleCover (Spec (CommRingCat.of R))) [IsAffine X.carrier]
variable (act : G →* CategoryTheory.Aut X)
variable [Module.Finite R (CoverSections X)]

local instance coverSectionsAlgebraInstance : Algebra R (CoverSections X) :=
  coverSectionsAlgebra R X
local instance coverSectionsActionInstance : MulSemiringAction G (CoverSections X) :=
  coverSectionsMulSemiringAction X act
local instance coverSectionsSMulCommClassInstance :
    SMulCommClass G R (CoverSections X) :=
  coverSectionsSMulCommClass X act

/-- The canonical scheme endomorphism from the cover action. -/
noncomputable def canonicalCoverAction (g : G) : X.carrier ⟶ X.carrier :=
  (coverAutSchemeIso X act g⁻¹).hom

/-- The canonical scheme action is invariant on the quotient projection. -/
theorem canonicalCoverAction_invariant (g : G) :
    canonicalCoverAction (R := R) (G := G) X act g ≫
        coverQuotientProjection (R := R) (G := G) X =
      coverQuotientProjection (R := R) (G := G) X := by
  unfold canonicalCoverAction coverQuotientProjection quotientProjection
  have h := coverSectionsSpecAut_agrees X act (g⁻¹)
  have hs : (coverSectionsSpecAut X act (g⁻¹)).hom =
      groupActionSpecAut (A := CoverSections X) (G := G) g := rfl
  rw [hs] at h
  calc
    (coverAutSchemeIso X act g⁻¹).hom ≫ X.carrier.isoSpec.hom ≫
        affineFixedPointQuotientMap R (CoverSections X) G
        = ((coverAutSchemeIso X act g⁻¹).hom ≫ X.carrier.isoSpec.hom) ≫
          affineFixedPointQuotientMap R (CoverSections X) G := by rw [Category.assoc]
    _ = (X.carrier.isoSpec.hom ≫
          groupActionSpecAut (A := CoverSections X) (G := G) g) ≫
          affineFixedPointQuotientMap R (CoverSections X) G := by rw [h]
    _ = X.carrier.isoSpec.hom ≫
          (groupActionSpecAut (A := CoverSections X) (G := G) g ≫
            affineFixedPointQuotientMap R (CoverSections X) G) := by rw [Category.assoc]
    _ = X.carrier.isoSpec.hom ≫
          affineFixedPointQuotientMap R (CoverSections X) G := by
      rw [groupActionSpecAut_comp_affineFixedPointQuotientMap]

/-- Project-facing canonical cover entry: finite, over Spec R, and invariant. -/
theorem projectAffineQuotientCoverEntry_canonical
    (hiso : X.carrier.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (CoverSections X))) = X.structureMap) :
    IsFinite (coverQuotientProjection (R := R) (G := G) X) ∧
      (coverQuotientProjection (R := R) (G := G) X ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R (fixedPointSubalgebra R (CoverSections X) G))) = X.structureMap) ∧
      (∀ g : G,
        canonicalCoverAction (R := R) (G := G) X act g ≫
          coverQuotientProjection (R := R) (G := G) X =
            coverQuotientProjection (R := R) (G := G) X) :=
  ⟨coverQuotientProjection_isFinite (R := R) (G := G) X,
    coverQuotientProjection_over (R := R) (G := G) X hiso,
    fun g => canonicalCoverAction_invariant (R := R) (G := G) X act g⟩

end LeanFormal.IUT.Foundations.AlgebraicGeometry.CoverActionCompatibilityFromSections
