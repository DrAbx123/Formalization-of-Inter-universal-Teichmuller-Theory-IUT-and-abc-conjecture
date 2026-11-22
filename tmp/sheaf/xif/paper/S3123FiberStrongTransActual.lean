import tmp.sheaf.xif.paper.S3123FiberNatTransActual
import Mathlib.CategoryTheory.Thin
noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S3123XKStackExtension
open LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceActual
open LeanFormal.IUT.XiFPaper.S3123FiberNatTransActual
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3123FiberStrongTransActual
variable {l : PrimeGeFive}
instance S3123DiscreteThin (J : Type) : Quiver.IsThin (Discrete J) :=
  fun _ _ => inferInstance
instance S3123CatHomSubsingleton {C D : Cat} [Quiver.IsThin D]
    (F G : C ⟶ D) : Subsingleton (F ⟶ G) := by
  constructor
  intro a b
  apply CategoryTheory.Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext X
  exact Subsingleton.elim _ _
set_option maxHeartbeats 800000 in
noncomputable def S3123FiberStrongTrans :
    Pseudofunctor.StrongTrans (S3123Left (l := l)) (S3123Right (l := l)) where
  app := S3123FiberApp (l := l)
  naturality := fun {a b} g => S3123FiberNatIso (l := l) g
  naturality_naturality := by
    intro a b f g eta
    let F := (S3123Left (l := l)).map f ≫ S3123FiberApp (l := l) b
    let G := S3123FiberApp (l := l) a ≫ (S3123Right (l := l)).map g
    haveI hthin : Quiver.IsThin ((S3123Right (l := l)).obj b) := by
      change Quiver.IsThin (Cat.of (Discrete _))
      exact S3123DiscreteThin _
    haveI hsub : Subsingleton (F ⟶ G) :=
      S3123CatHomSubsingleton (C := (S3123Left (l := l)).obj a)
        (D := (S3123Right (l := l)).obj b) F G
    exact Subsingleton.elim _ _
  naturality_id := by
    intro a
    let F := (S3123Left (l := l)).map (𝟙 a) ≫ S3123FiberApp (l := l) a
    let G := S3123FiberApp (l := l) a ≫ 𝟙 ((S3123Right (l := l)).obj a)
    haveI hthin : Quiver.IsThin ((S3123Right (l := l)).obj a) := by
      change Quiver.IsThin (Cat.of (Discrete _))
      exact S3123DiscreteThin _
    haveI hsub : Subsingleton (F ⟶ G) :=
      S3123CatHomSubsingleton (C := (S3123Left (l := l)).obj a)
        (D := (S3123Right (l := l)).obj a) F G
    exact Subsingleton.elim _ _
  naturality_comp := by
    intro a b c f g
    let F := (S3123Left (l := l)).map (f ≫ g) ≫ S3123FiberApp (l := l) c
    let G := S3123FiberApp (l := l) a ≫ (S3123Right (l := l)).map f ≫
      (S3123Right (l := l)).map g
    haveI hthin : Quiver.IsThin ((S3123Right (l := l)).obj c) := by
      change Quiver.IsThin (Cat.of (Discrete _))
      exact S3123DiscreteThin _
    haveI hsub : Subsingleton (F ⟶ G) :=
      S3123CatHomSubsingleton (C := (S3123Left (l := l)).obj a)
        (D := (S3123Right (l := l)).obj c) F G
    exact Subsingleton.elim _ _
#check S3123FiberStrongTrans
end LeanFormal.IUT.XiFPaper.S3123FiberStrongTransActual
end
