import tmp.sheaf.xif.paper.S3127G2UniversalParamActual
import tmp.sheaf.xif.paper.S3127G2ActionBaseActual
import tmp.sheaf.xif.paper.S3127FreeQuotientActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.XiFPaper.S3127G2UniversalParamActual
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
namespace LeanFormal.IUT.XiFPaper.S3127G2UniversalTargetActual
variable {l : PrimeGeFive} {G : Type} [Group G]

theorem S3127G2QuotientUniversalOf
    (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
    [Fintype G]
    (hfree : forall (x : A.obj.left.left) (g : G),
      (S3127G2Action A act g).hom.left.left x = x -> g = 1)
    (Qobj : S3127FiniteEtaleOverKFull l)
    (q : A ⟶ Qobj)
    (hq : forall g : G, S3127G2Action A act g ≫ q = q)
    (phi : forall {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B),
      (forall g : G, S3127G2Action A act g ≫ f = f) -> Prop)
    (hphi : forall {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
      (hinv : forall g : G, S3127G2Action A act g ≫ f = f), phi f hinv)
    (hfac : forall {B : S3127FiniteEtaleOverKFull l} (f : A ⟶ B)
      (hinv : forall g : G, S3127G2Action A act g ≫ f = f),
      ∃! v_raw : S3127FullForget.obj Qobj ⟶ S3127FullForget.obj B,
        S3127FullForget.map q ≫ v_raw = S3127FullForget.map f) :
    S3127QuotientUniversal
      { action := S3127G2Action A act
        action_one := S3127G2Action_one A act
        action_mul := S3127G2Action_mul A act
        free := hfree
        quotientObj := Qobj
        quotientMap := q
        invariant := hq } := by
  exact S3127G2Universal_of_phi A act Qobj q phi hphi hfac

#check S3127G2QuotientUniversalOf
end LeanFormal.IUT.XiFPaper.S3127G2UniversalTargetActual
end