import tmp.sheaf.xif.paper.S3128CoproductSimplificationActual
import tmp.sheaf.xif.paper.S3128OverForgetPreservesActual
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S3128ZMod2FiberCategoryActual
open LeanFormal.IUT.XiFPaper.S3128CoproductSimplificationActual
open LeanFormal.IUT.XiFPaper.S3128ZMod2BaseChangeActual
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.S3128OverCoproductLeftActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}
variable {U U' : SchemeOverField F} (A : S3128ZMod2FiberObj (F := F) X U)

abbrev S3128OverIndexFamily : WalkingPair → SchemeOverField F :=
  fun i => match i with
    | WalkingPair.left => A.P
    | WalkingPair.right => A.P

noncomputable def S3128OverWalkingPairBinaryIso
    (Q : SchemeOverField F) :
    (∐ (fun i : WalkingPair =>
      match i with
      | WalkingPair.left => Q
      | WalkingPair.right => Q)) ≅ (Q ⨿ Q) where
  hom := Sigma.desc (fun i : WalkingPair =>
    match i with
    | WalkingPair.left => coprod.inl
    | WalkingPair.right => coprod.inr)
  inv := coprod.desc
    (Sigma.ι (fun i : WalkingPair =>
      match i with
      | WalkingPair.left => Q
      | WalkingPair.right => Q) WalkingPair.left)
    (Sigma.ι (fun i : WalkingPair =>
      match i with
      | WalkingPair.left => Q
      | WalkingPair.right => Q) WalkingPair.right)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    cases i
    · rw [← Category.assoc, Sigma.ι_desc]
      simp [coprod.inl_desc]
    · rw [← Category.assoc, Sigma.ι_desc]
      simp [coprod.inr_desc]
  inv_hom_id := by
    apply coprod.hom_ext <;> simp [Sigma.ι_desc]

theorem S3128OverIndexFamily_forget :
    (fun j : WalkingPair =>
      (Over.forget (Spec (CommRingCat.of F))).obj
        (S3128OverIndexFamily A j)) =
    (fun j : WalkingPair =>
      match j with
      | WalkingPair.left => Over.left A.P
      | WalkingPair.right => Over.left A.P) := by
  funext j
  cases j <;> rfl

noncomputable def S3128OverCoproductLeftIso :
    (A.P ⨿ A.P).left ≅ (A.P.left ⨿ A.P.left) :=
  eqToIso (show Over.left (A.P ⨿ A.P) =
      (Over.forget (Spec (CommRingCat.of F))).obj (A.P ⨿ A.P) from rfl)
    ≪≫ (Over.forget (Spec (CommRingCat.of F))).mapIso
      (S3128OverWalkingPairBinaryIso A.P).symm
    ≪≫ PreservesCoproduct.iso
      (Over.forget (Spec (CommRingCat.of F)))
      (S3128OverIndexFamily A)
    ≪≫ eqToIso (congrArg (fun F => ∐ F) (S3128OverIndexFamily_forget A))
    ≪≫ S3128WalkingPairBinaryIso (Over.left A.P)

noncomputable def S3128OverUnitCoproductIso :
    (∐ (fun _ : Unit => Over.left U') : Scheme) ≅ Over.left U' :=
  S3128UnitCoproductIso (F := F) (U' := U')

noncomputable def S3128OverUnitCoproductIsoSymm :
    Over.left U' ≅ (∐ (fun _ : Unit => Over.left U') : Scheme) :=
  (S3128OverUnitCoproductIso (F := F) (U' := U')).symm

#check S3128OverCoproductLeftIso
#print axioms S3128OverCoproductLeftIso

end LeanFormal.IUT.XiFPaper.S3128OverCoproductLeftActual