import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientActionDataFromCover
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleCoverActionFunctor

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

/-!
# Scheme-level affine quotient action cocone (S2 candidate)

Declaration-stage candidate: the quotient scheme and projection are actual;
the cocone naturality is proved from the actual carrier projection invariance.
The scheme-level IsColimit statement remains an explicit residual: the
existing universal property is affine-target only and does not supply a desc
map for an arbitrary scheme cocone.  This is NOT the source-cover-category G2
colimit.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open ABCBridge.AffineQuotientActionDataFromCover
open ABCBridge.CoverSectionsAction
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleCoverActionFunctor
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient

namespace LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientCoconeIsColimit

universe u

variable {R : Type u} [CommRing R]
  {G : Type u} [Group G]
  (X : FiniteEtaleCover (Spec (CommRingCat.of R)))
  (act : G →* CategoryTheory.Aut X)

abbrev base (R : Type u) [CommRing R] : Scheme.{u} :=
  Spec (CommRingCat.of R)

/-- Forget a finite-etale cover to its underlying scheme. -/
abbrev coverToScheme (R : Type u) [CommRing R] :
    FiniteEtaleCover (base R) ⥤ Scheme.{u} :=
  FiniteEtaleCover.forgetOver (base R) ⋙ Over.forget (base R)

/-- Scheme-level action functor underlying the cover action. -/
noncomputable abbrev schemeActionFunctor : SingleObj G ⥤ Scheme.{u} :=
  actionFunctorOfAction (R := R) X act ⋙ coverToScheme R

/-- The scheme-level quotient Spec (Gamma(X)^G). -/
noncomputable abbrev quotientScheme : Scheme.{u} := actualQuotientScheme X act

/-- The scheme-level quotient projection X.carrier to Spec (Gamma(X)^G). -/
noncomputable abbrev quotientProjection : X.carrier ⟶ quotientScheme (R := R) X act :=
  actualCarrierProjection X act

/-- Invariance of the actual carrier projection under the scheme-level cover action. -/
theorem actualCarrierProjection_invariant (g : G) :
    (coverAutSchemeIso X act g).hom ≫ actualCarrierProjection X act =
      actualCarrierProjection X act := by
  letI := coverAction X act
  letI := coverActionComm X act
  rw [actualCarrierProjection_eq]
  change (coverAutSchemeIso X act g).hom ≫ X.carrier.isoSpec.hom ≫
      affineFixedPointQuotientMap R (CoverCoordinateAlgebra X) G =
    X.carrier.isoSpec.hom ≫
      affineFixedPointQuotientMap R (CoverCoordinateAlgebra X) G
  have hnat := coverSectionsSpecAut_agrees X act g
  have hgroup : (coverSectionsSpecAut X act g).hom =
      groupActionSpecAut (A := CoverCoordinateAlgebra X) (G := G) g⁻¹ := by
    unfold coverSectionsSpecAut groupActionSpecAut groupActionRingEquiv
    apply congrArg Spec.map
    apply congrArg CommRingCat.ofHom
    ext x
    change coverSectionsRingEquiv X act g x =
      coverSectionsRingEquiv X act ((g⁻¹)⁻¹) x
    rw [inv_inv]
  have hnat' : X.carrier.isoSpec.hom ≫
      groupActionSpecAut (A := CoverCoordinateAlgebra X) (G := G) g⁻¹ =
        (coverAutSchemeIso X act g).hom ≫ X.carrier.isoSpec.hom := by
    simpa [coverSectionsIsoSpec, hgroup] using hnat
  calc
    (coverAutSchemeIso X act g).hom ≫ X.carrier.isoSpec.hom ≫
        affineFixedPointQuotientMap R (CoverCoordinateAlgebra X) G
        = ((coverAutSchemeIso X act g).hom ≫ X.carrier.isoSpec.hom) ≫
            affineFixedPointQuotientMap R (CoverCoordinateAlgebra X) G := by
          rw [Category.assoc]
    _ = (X.carrier.isoSpec.hom ≫
          groupActionSpecAut (A := CoverCoordinateAlgebra X) (G := G) g⁻¹) ≫
            affineFixedPointQuotientMap R (CoverCoordinateAlgebra X) G := by
          rw [← hnat']
    _ = X.carrier.isoSpec.hom ≫
          (groupActionSpecAut (A := CoverCoordinateAlgebra X) (G := G) g⁻¹ ≫
            affineFixedPointQuotientMap R (CoverCoordinateAlgebra X) G) := by
          rw [Category.assoc]
    _ = X.carrier.isoSpec.hom ≫
          affineFixedPointQuotientMap R (CoverCoordinateAlgebra X) G := by
          rw [groupActionSpecAut_comp_affineFixedPointQuotientMap]

/-- Scheme-level cocone candidate over the action functor. -/
noncomputable def quotientCocone : Cocone (schemeActionFunctor (R := R) X act) :=
  Cocone.mk (quotientScheme (R := R) X act)
    (NatTrans.mk (fun _ => quotientProjection (R := R) X act) (by
      intro X' Y' f
      cases X'
      cases Y'
      change (coverAutSchemeIso X act f).hom ≫
          quotientProjection (R := R) X act =
        quotientProjection (R := R) X act
      exact actualCarrierProjection_invariant X act f))

/-- Exact residual: the scheme-level colimit proof for the actual cocone. -/
def quotientCoconeIsColimitResidual : Type _ :=
  IsColimit (quotientCocone (R := R) X act)

/-- Conditional consumer: the missing scheme-level colimit proof is an explicit
input, not an axiom and not a sorry. -/
noncomputable def quotientCocone_isColimit_of_residual
    (h : quotientCoconeIsColimitResidual X act) :
    IsColimit (quotientCocone (R := R) X act) :=
  h

end LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineQuotientCoconeIsColimit

end