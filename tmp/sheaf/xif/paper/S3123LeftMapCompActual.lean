import tmp.sheaf.xif.paper.S3123LeftMapIdActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S3123XKStackExtension
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceActual
open LeanFormal.IUT.XiFPaper.S3123FiberNatTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransActual
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransInvActual
open LeanFormal.IUT.XiFPaper.S3123LeftCoeActual
open LeanFormal.IUT.XiFPaper.S3123LeftExplicitActual
open LeanFormal.IUT.XiFPaper.S3123LeftMapActual
open LeanFormal.IUT.XiFPaper.S3123LeftMapIdActual

namespace LeanFormal.IUT.XiFPaper.S3123LeftMapCompActual

variable {l : PrimeGeFive}

set_option maxHeartbeats 800000 in
noncomputable def S3123LeftMapComp
    {U V W : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (f : U ⟶ V) (g : V ⟶ W) :
    S3123LeftMap (l := l) (f ≫ g) ≅
      S3123LeftMap (l := l) f ≫ S3123LeftMap (l := l) g := by
  have hUV : (S3123Left (l := l)).obj U = S3123LeftObj (l := l) U :=
    (S3123LeftObj_eq (l := l) U).symm
  have hVW : (S3123Left (l := l)).obj V = S3123LeftObj (l := l) V :=
    (S3123LeftObj_eq (l := l) V).symm
  have hUW : (S3123Left (l := l)).obj U = S3123LeftObj (l := l) U :=
    (S3123LeftObj_eq (l := l) U).symm
  let oldComp := (S3123Left (l := l)).map (f ≫ g)
  let oldF := (S3123Left (l := l)).map f
  let oldG := (S3123Left (l := l)).map g
  have hCompType :
      ((S3123Left (l := l)).obj U ⟶ (S3123Left (l := l)).obj W) =
        (S3123LeftObj (l := l) U ⟶ S3123LeftObj (l := l) W) :=
    congrArg₂ (fun (A B : Cat) => (A ⟶ B)) hUW
      (S3123LeftObj_eq (l := l) W).symm
  have hFType :
      ((S3123Left (l := l)).obj U ⟶ (S3123Left (l := l)).obj V) =
        (S3123LeftObj (l := l) U ⟶ S3123LeftObj (l := l) V) :=
    congrArg₂ (fun (A B : Cat) => (A ⟶ B)) hUV
      (S3123LeftObj_eq (l := l) V).symm
  have hGType :
      ((S3123Left (l := l)).obj V ⟶ (S3123Left (l := l)).obj W) =
        (S3123LeftObj (l := l) V ⟶ S3123LeftObj (l := l) W) :=
    congrArg₂ (fun (A B : Cat) => (A ⟶ B)) hVW
      (S3123LeftObj_eq (l := l) W).symm
  have hCompType_rfl : hCompType = rfl := Subsingleton.elim _ _
  have hFType_rfl : hFType = rfl := Subsingleton.elim _ _
  have hGType_rfl : hGType = rfl := Subsingleton.elim _ _
  have hmapComp : S3123LeftMap (l := l) (f ≫ g) = cast hCompType oldComp := rfl
  have hmapF : S3123LeftMap (l := l) f = cast hFType oldF := rfl
  have hmapG : S3123LeftMap (l := l) g = cast hGType oldG := rfl
  rw [hmapComp, hmapF, hmapG, hCompType_rfl, hFType_rfl, hGType_rfl]
  exact (S3123Left (l := l)).mapComp f g

#check S3123LeftMapComp

end LeanFormal.IUT.XiFPaper.S3123LeftMapCompActual
end
