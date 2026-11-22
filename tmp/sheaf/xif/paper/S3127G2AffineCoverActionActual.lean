import tmp.sheaf.xif.paper.S3127G2CoverIsoActual
import tmp.sheaf.xif.paper.S3127G2ActionBaseActual
import tmp.sheaf.xif.paper.S3127FreeQuotientActual
import tmp.sheaf.xif.paper.S3127FullForgetActual
import tmp.sheaf.xif.paper.S3127GammaActionActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127GammaActionActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2CoverIsoActual
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2AffineCoverActionActual
variable {l : PrimeGeFive} {G : Type} [Group G]

/-- The actual anabelian action endomorphism of the raw finite-etale cover as an
isomorphism: the Over automorphism of `Over.mk A.obj.hom.left` determined by the
actual scheme automorphism `act.act g` and the `Over`-condition `act.overR`. -/
noncomputable def S3127G2RawCoverAction
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g : G) :
    S3127G2RawCoverA A ≅ S3127G2RawCoverA A :=
  ObjectProperty.isoMk
    (P := fun X : Over (S1419AffineScheme l) => IsFiniteEtaleHom X.hom)
    ((Over.isoMk (f := (S3127G2RawCoverA A).obj) (g := (S3127G2RawCoverA A).obj)
      (act.act g) (act.overR g)).symm)

/-- The affine cover self-map induced by `act g`: conjugation of the actual raw
cover action by the actual cover isomorphism `S3127G2CoverIsoA`.  This is an
isomorphism by construction, so no separate over-square is needed. -/
noncomputable def S3127G2AffineCoverAction
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g : G) :
    S3127G2AffineCoverA A ≅ S3127G2AffineCoverA A :=
  (S3127G2CoverIsoA A).symm ≪≫ S3127G2RawCoverAction A act g ≪≫ (S3127G2CoverIsoA A)

/-- The underlying scheme map of the raw cover action is `(act g)⁻¹`. -/
theorem S3127G2RawCoverAction_hom_left
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g : G) :
    Over.Hom.left ((S3127G2RawCoverAction A act g).hom.hom) = (act.act g).inv :=
  rfl

/-- The raw cover action is exactly the full-forget image of the anabelian action
`S3127G2Action`. -/
theorem S3127G2FullForget_map_raw
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g : G) :
    S3127FullForget.map (S3127G2Action A act g) =
      (S3127G2RawCoverAction A act g).hom := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  first
    | rfl
    | (rw [S3127FullForget_map_hom_left, S3127G2RawCoverAction_hom_left]; rfl)

/-- The hom of the affine cover action, as a conjugated raw action. -/
theorem S3127G2AffineCoverAction_hom
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g : G) :
    (S3127G2AffineCoverAction A act g).hom =
      (S3127G2CoverIsoA A).inv ≫ (S3127G2RawCoverAction A act g).hom ≫
        (S3127G2CoverIsoA A).hom :=
  rfl

/-- Underlying scheme map of the affine cover action: conjugation of
`(act g)⁻¹` by the affine `isoSpec`. -/
theorem S3127G2AffineCoverAction_hom_left
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g : G) :
    Over.Hom.left ((S3127G2AffineCoverAction A act g).hom.hom) =
      A.obj.left.left.isoSpec.inv ≫ (act.act g).inv ≫
        A.obj.left.left.isoSpec.hom :=
  rfl

#check S3127G2RawCoverAction
#check S3127G2AffineCoverAction
#check S3127G2RawCoverAction_hom_left
#check S3127G2FullForget_map_raw
#check S3127G2AffineCoverAction_hom
#check S3127G2AffineCoverAction_hom_left
end LeanFormal.IUT.XiFPaper.S3127G2AffineCoverActionActual
end
