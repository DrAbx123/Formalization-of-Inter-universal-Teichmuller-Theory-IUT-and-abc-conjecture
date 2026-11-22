import tmp.sheaf.xif.paper.S3123FiberNatTransTarget
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
open LeanFormal.IUT.XiFPaper.S3123FiberNatTrans

namespace LeanFormal.IUT.XiFPaper.S3123FiberNatTransActual

variable {l : PrimeGeFive}

@[simp] lemma S3123FiberApp_apply
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ)
    (P : Opposite.unop U.as ⟶ S3123BaseChangedScheme (l := l)) :
    (S3123FiberApp (l := l) U).toFunctor.obj (Discrete.mk P) =
      Discrete.mk (((Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
        (Opposite.unop U.as) (S1419AffineOver (l := l))).symm P) := rfl

@[simp] lemma S3123Left_map_apply
    {a b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (g : a ⟶ b) (P : (S3123Left (l := l)).obj a) :
    ((S3123Left (l := l)).map g).toFunctor.obj P =
      Discrete.mk (g.as.unop ≫ P.as) := rfl

@[simp] lemma S3123Right_map_apply
    {a b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (g : a ⟶ b) (P : (S3123Right (l := l)).obj a) :
    ((S3123Right (l := l)).map g).toFunctor.obj P =
      Discrete.mk ((schemeRestrictScalars
        (S1280Arithmetic l).F (S1280Arithmetic l).K).map g.as.unop ≫ P.as) := rfl

#check S3123FiberApp_apply
#check S3123Left_map_apply
#check S3123Right_map_apply



instance S3123DiscreteThin (J : Type) : Quiver.IsThin (Discrete J) :=
  fun _ _ => inferInstance

instance S3123DiscreteHomSubsingleton (I : Type) (X Y : Discrete I) :
    Subsingleton (X ⟶ Y) :=
  Discrete.instSubsingletonDiscreteHom X Y

instance S3123CatHomSubsingleton {C D : Cat} [Quiver.IsThin D]
    (F G : C ⟶ D) : Subsingleton (F ⟶ G) := by
  constructor
  intro a b
  apply CategoryTheory.Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext X
  exact Subsingleton.elim _ _

noncomputable def S3123FiberNatTrans
    {a b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (g : a ⟶ b) : S3123FiberNatTransTarget (l := l) g :=
  { toNatTrans :=
    { app := fun X => by
        rcases X with ⟨P⟩
        apply Discrete.eqToHom
        change ((Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
              (Opposite.unop b.as) (S1419AffineOver (l := l))).symm
                (g.as.unop ≫ P) =
          (schemeRestrictScalars (S1280Arithmetic l).F
              (S1280Arithmetic l).K).map g.as.unop ≫
              ((Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
                (Opposite.unop a.as) (S1419AffineOver (l := l))).symm P
        let adj := Over.mapPullbackAdj (S3123BaseSpecMap (l := l))
        let S := S1419AffineOver (l := l)
        let Q := (adj.homEquiv (Opposite.unop a.as) S).symm P
        apply (adj.homEquiv (Opposite.unop b.as) S).injective
        change (adj.homEquiv (Opposite.unop b.as) S)
            ((adj.homEquiv (Opposite.unop b.as) S).symm (g.as.unop ≫ P)) =
          (adj.homEquiv (Opposite.unop b.as) S)
            ((schemeRestrictScalars (S1280Arithmetic l).F
              (S1280Arithmetic l).K).map g.as.unop ≫ Q)
        rw [show (adj.homEquiv (Opposite.unop b.as) S)
              ((adj.homEquiv (Opposite.unop b.as) S).symm (g.as.unop ≫ P)) =
              g.as.unop ≫ P from Equiv.apply_symm_apply _ _]
        change g.as.unop ≫ P =
          (adj.homEquiv (Opposite.unop b.as) S)
            ((Over.map (S3123BaseSpecMap (l := l))).map g.as.unop ≫ Q)
        rw [Adjunction.homEquiv_naturality_left]
        rw [show (adj.homEquiv (Opposite.unop a.as) S) Q = P from
              Equiv.apply_symm_apply _ _]
      naturality := fun X Y f => by
        haveI : Subsingleton
            ((((S3123Left (l := l)).map g ≫ S3123FiberApp (l := l) b).toFunctor.obj X) ⟶
              (((S3123FiberApp (l := l) a ≫ (S3123Right (l := l)).map g).toFunctor.obj Y))) := by
          change Subsingleton ((Discrete.mk _) ⟶ (Discrete.mk _))
          exact S3123DiscreteHomSubsingleton _ _ _
        exact Subsingleton.elim _ _ } }

#check S3123FiberNatTrans



noncomputable def S3123DiscreteIsoOfHom {I : Type} {X Y : Discrete I}
    (f : X ⟶ Y) : X ≅ Y :=
  { hom := f
    inv := Discrete.eqToHom (Discrete.eq_of_hom f).symm
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }

noncomputable def S3123FiberNatIso
    {a b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (g : a ⟶ b) :
    (S3123Left (l := l)).map g ≫ S3123FiberApp (l := l) b ≅
      S3123FiberApp (l := l) a ≫ (S3123Right (l := l)).map g :=
  CategoryTheory.Cat.Hom.isoMk
    (NatIso.ofComponents
      (fun X => S3123DiscreteIsoOfHom
        ((S3123FiberNatTrans (l := l) g).toNatTrans.app X))
      (fun {X Y} f => by
        haveI : Subsingleton
            ((((S3123Left (l := l)).map g).toFunctor ⋙
                (S3123FiberApp (l := l) b).toFunctor).obj X ⟶
              (((S3123FiberApp (l := l) a).toFunctor ⋙
                ((S3123Right (l := l)).map g).toFunctor)).obj Y) := by
          change Subsingleton ((Discrete.mk _) ⟶ (Discrete.mk _))
          exact S3123DiscreteHomSubsingleton _ _ _
        exact Subsingleton.elim _ _))

#check S3123FiberNatIso
end LeanFormal.IUT.XiFPaper.S3123FiberNatTransActual
end
