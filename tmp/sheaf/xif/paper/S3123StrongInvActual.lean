import tmp.sheaf.xif.paper.S3123InvAppActual
import tmp.sheaf.xif.paper.S3123InvNatActual
import tmp.sheaf.xif.paper.S3123ObjEqActual

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
open LeanFormal.IUT.XiFPaper.S3123InvAppActual
open LeanFormal.IUT.XiFPaper.S3123InvNatActual
open LeanFormal.IUT.XiFPaper.S3123ObjEqActual

namespace LeanFormal.IUT.XiFPaper.S3123StrongInvActual

variable {l : PrimeGeFive}

set_option maxHeartbeats 800000 in
noncomputable def S3123FiberStrongTransInv :
    Pseudofunctor.StrongTrans (S3123Right (l := l)) (S3123Left (l := l)) where
  app := S3123FiberAppInv (l := l)
  naturality := fun {a b} g => by
    apply eqToIso
    apply CategoryTheory.Cat.ext
    apply CategoryTheory.Discrete.functor_ext
    intro Q
    rw [CategoryTheory.Cat.Hom.comp_toFunctor, Functor.comp_obj]
    rw [S3123Right_map_apply]
    change (S3123FiberAppInv (l := l) b).toFunctor.obj
        (Discrete.mk ((schemeRestrictScalars (S1280Arithmetic l).F
          (S1280Arithmetic l).K).map g.as.unop ≫ Q)) =
      (S3123FiberAppInv (l := l) a ≫
        (S3123Left (l := l)).map g).toFunctor.obj (Discrete.mk Q)
    rw [S3123FiberAppInv_apply]
    rw [CategoryTheory.Cat.Hom.comp_toFunctor, Functor.comp_obj]
    rw [S3123FiberAppInv_apply, S3123Left_map_apply]
    apply Discrete.ext
    exact Adjunction.homEquiv_naturality_left
      (adj := Over.mapPullbackAdj (S3123BaseSpecMap (l := l)))
      (f := g.as.unop) (g := Q)
  naturality_naturality := by
    intro a b f g eta
    let F := (S3123Right (l := l)).map f ≫ S3123FiberAppInv (l := l) b
    let G := S3123FiberAppInv (l := l) a ≫ (S3123Left (l := l)).map g
    haveI hthin : Quiver.IsThin ((S3123Left (l := l)).obj b) := by
      change Quiver.IsThin (Cat.of (Discrete _))
      exact S3123FiberStrongTransActual.S3123DiscreteThin _
    haveI hsub : Subsingleton (F ⟶ G) :=
      S3123FiberStrongTransActual.S3123CatHomSubsingleton
        (C := (S3123Right (l := l)).obj a)
        (D := (S3123Left (l := l)).obj b) F G
    exact Subsingleton.elim _ _
  naturality_id := by
    intro a
    let F := (S3123Right (l := l)).map (𝟙 a) ≫ S3123FiberAppInv (l := l) a
    let G := S3123FiberAppInv (l := l) a ≫ 𝟙 ((S3123Left (l := l)).obj a)
    haveI hthin : Quiver.IsThin ((S3123Left (l := l)).obj a) := by
      change Quiver.IsThin (Cat.of (Discrete _))
      exact S3123FiberStrongTransActual.S3123DiscreteThin _
    haveI hsub : Subsingleton (F ⟶ G) :=
      S3123FiberStrongTransActual.S3123CatHomSubsingleton
        (C := (S3123Right (l := l)).obj a)
        (D := (S3123Left (l := l)).obj a) F G
    exact Subsingleton.elim _ _
  naturality_comp := by
    intro a b c f g
    let F := (S3123Right (l := l)).map (f ≫ g) ≫ S3123FiberAppInv (l := l) c
    let G := S3123FiberAppInv (l := l) a ≫ (S3123Left (l := l)).map f ≫
      (S3123Left (l := l)).map g
    haveI hthin : Quiver.IsThin ((S3123Left (l := l)).obj c) := by
      change Quiver.IsThin (Cat.of (Discrete _))
      exact S3123FiberStrongTransActual.S3123DiscreteThin _
    haveI hsub : Subsingleton (F ⟶ G) :=
      S3123FiberStrongTransActual.S3123CatHomSubsingleton
        (C := (S3123Right (l := l)).obj a)
        (D := (S3123Left (l := l)).obj c) F G
    exact Subsingleton.elim _ _



#check S3123FiberStrongTransInv

end LeanFormal.IUT.XiFPaper.S3123StrongInvActual
end
