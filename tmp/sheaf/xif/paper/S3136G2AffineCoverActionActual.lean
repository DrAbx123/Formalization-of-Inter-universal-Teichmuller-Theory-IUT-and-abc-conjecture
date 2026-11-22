import tmp.sheaf.xif.paper.S3127G2AffineCoverActionActual
import tmp.sheaf.xif.paper.S3127G2ActionCoverNaturalActual
import tmp.sheaf.xif.paper.S3127G2ActionBaseActual
import tmp.sheaf.xif.paper.S3127G2CoverIsoActual
import tmp.sheaf.xif.paper.S3127FullForgetActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2CoverIsoActual
open LeanFormal.IUT.XiFPaper.S3127G2AffineCoverActionActual
open LeanFormal.IUT.XiFPaper.S3127G2ActionCoverNaturalActual
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3136G2AffineCoverActionActual
variable {l : PrimeGeFive} {G : Type} [Group G]

/-- Conjugation form of the affine cover action, expressed through the
full-forget image of the anabelian action. -/
theorem S3127G2AffineCoverAction_hom_via
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g : G) :
    (S3127G2AffineCoverAction A act g).hom =
      (S3127G2CoverIsoA A).inv ≫
        S3127FullForget.map (S3127G2Action A act g) ≫ (S3127G2CoverIsoA A).hom := by
  exact (S3127G2AffineCoverAction_hom A act g).trans (congrArg
    (fun m => (S3127G2CoverIsoA A).inv ≫ m ≫ (S3127G2CoverIsoA A).hom)
    (S3127G2FullForget_map_raw A act g)).symm

/-- The group law at the identity for the affine cover action. -/
theorem S3127G2AffineCoverAction_one
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) :
    S3127G2AffineCoverAction A act (1 : G) = Iso.refl (S3127G2AffineCoverA A) := by
  apply Iso.ext
  rw [S3127G2AffineCoverAction_hom_via, S3127G2Action_one]
  have hmap : (S3127FullForget (l := l)).map (𝟙 A) =
      𝟙 (S3127FullForget.obj A) :=
    (S3127FullForget (l := l)).map_id A
  rw [hmap]
  simp only [Category.id_comp, Iso.refl_hom]
  exact Iso.inv_hom_id (S3127G2CoverIsoA A)

/-- Multiplicativity of the raw cover action, proved through the full-forget
image of the anabelian action (no Hom-level cancellation across the cover
isomorphism is needed for this step). -/
theorem S3127G2RawCoverAction_mul
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g h : G) :
    S3127G2RawCoverAction A act (g * h) =
      (S3127G2RawCoverAction A act g).trans (S3127G2RawCoverAction A act h) := by
  apply Iso.ext
  rw [Iso.trans_hom]
  have e1 : (S3127G2RawCoverAction A act (g * h)).hom =
      S3127FullForget.map (S3127G2Action A act (g * h)) :=
    (S3127G2FullForget_map_raw A act (g * h)).symm
  have e2 : S3127FullForget.map (S3127G2Action A act (g * h)) =
      S3127FullForget.map (S3127G2Action A act g ≫ S3127G2Action A act h) :=
    congrArg (fun m => S3127FullForget.map m) (S3127G2Action_mul A act g h)
  have e3 : S3127FullForget.map (S3127G2Action A act g ≫ S3127G2Action A act h) =
      S3127FullForget.map (S3127G2Action A act g) ≫
        S3127FullForget.map (S3127G2Action A act h) :=
    (S3127FullForget (l := l)).map_comp _ _
  have e4 : S3127FullForget.map (S3127G2Action A act g) ≫
        S3127FullForget.map (S3127G2Action A act h) =
      (S3127G2RawCoverAction A act g).hom ≫
        (S3127G2RawCoverAction A act h).hom :=
    (congrArg (fun m => m ≫ S3127FullForget.map (S3127G2Action A act h))
      (S3127G2FullForget_map_raw A act g)).trans
      (congrArg (fun m => (S3127G2RawCoverAction A act g).hom ≫ m)
        (S3127G2FullForget_map_raw A act h))
  exact e1.trans (e2.trans (e3.trans e4))

/-- Multiplicativity of the affine cover action, in the composition order of
`S3127G2Action_mul`. -/
theorem S3127G2AffineCoverAction_mul
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g h : G) :
    S3127G2AffineCoverAction A act (g * h) =
      (S3127G2AffineCoverAction A act g).trans (S3127G2AffineCoverAction A act h) := by
  apply Iso.ext
  rw [Iso.trans_hom]
  simp only [S3127G2AffineCoverAction_hom]
  rw [S3127G2RawCoverAction_mul, Iso.trans_hom]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_assoc]

/-- Underlying scheme map of the affine cover action: conjugation of
`(act g)⁻¹` by the affine `isoSpec`. -/
theorem S3127G2AffineCoverAction_left
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) (g : G) :
    Over.Hom.left ((S3127G2AffineCoverAction A act g).hom.hom) =
      A.obj.left.left.isoSpec.inv ≫ (act.act g).inv ≫
        A.obj.left.left.isoSpec.hom :=
  S3127G2AffineCoverAction_hom_left A act g

/-- The actual affine-cover action as a monoid homomorphism on the opposite
group: `Gᵐᵒᵖ →* Aut (S3127G2AffineCoverA A)`.  The opposite group appears
because `CategoryTheory.Aut` multiplies as `x * y = y ≪≫ x`, while the
anabelian action composes in the source order. -/
noncomputable def S3127G2AffineCoverActionHom
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G) :
    (Gᵐᵒᵖ) →* Aut (S3127G2AffineCoverA A) where
  toFun g := S3127G2AffineCoverAction A act (MulOpposite.unop g)
  map_one' := S3127G2AffineCoverAction_one A act
  map_mul' g h := by
    have hu : MulOpposite.unop (g * h) =
        MulOpposite.unop h * MulOpposite.unop g := rfl
    rw [hu]
    exact S3127G2AffineCoverAction_mul A act (MulOpposite.unop h) (MulOpposite.unop g)

#check S3127G2AffineCoverAction_hom_via
#check S3127G2AffineCoverAction_one
#check S3127G2AffineCoverAction_mul
#check S3127G2RawCoverAction_mul
#check S3127G2AffineCoverAction_left
#check S3127G2AffineCoverActionHom
end LeanFormal.IUT.XiFPaper.S3136G2AffineCoverActionActual
end
