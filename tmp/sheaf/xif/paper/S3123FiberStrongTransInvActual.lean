import tmp.sheaf.xif.paper.S3123FiberStrongTransActual

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
open LeanFormal.IUT.XiFPaper.S3123FiberStrongTransActual

namespace LeanFormal.IUT.XiFPaper.S3123FiberStrongTransInvActual

variable {l : PrimeGeFive}

noncomputable def S3123FiberAppInv
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (S3123Right (l := l)).obj U ⟶ (S3123Left (l := l)).obj U :=
  (Discrete.functor (fun Q : (schemeRestrictScalars (S1280Arithmetic l).F
      (S1280Arithmetic l).K).obj (Opposite.unop U.as) ⟶ S1419AffineOver (l := l) =>
    Discrete.mk (((Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
      (Opposite.unop U.as) (S1419AffineOver (l := l))) Q))).toCatHom

@[simp] lemma S3123FiberAppInv_apply
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ)
    (Q : (schemeRestrictScalars (S1280Arithmetic l).F
      (S1280Arithmetic l).K).obj (Opposite.unop U.as) ⟶ S1419AffineOver (l := l)) :
    (S3123FiberAppInv (l := l) U).toFunctor.obj (Discrete.mk Q) =
      Discrete.mk (((Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
        (Opposite.unop U.as) (S1419AffineOver (l := l))) Q) := rfl

lemma S3123FiberNatTransInv_app_eq
    {a b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (g : a ⟶ b)
    (Q : (schemeRestrictScalars (S1280Arithmetic l).F
      (S1280Arithmetic l).K).obj (Opposite.unop a.as) ⟶
      S1419AffineOver (l := l)) :
    ((Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
        (Opposite.unop b.as) (S1419AffineOver (l := l)))
        ((schemeRestrictScalars (S1280Arithmetic l).F
          (S1280Arithmetic l).K).map g.as.unop ≫ Q) =
      g.as.unop ≫
        ((Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
          (Opposite.unop a.as) (S1419AffineOver (l := l))) Q := by
  simpa only [S3123BaseSpecMap, schemeRestrictScalars] using
    (Adjunction.homEquiv_naturality_left
      (adj := Over.mapPullbackAdj (S3123BaseSpecMap (l := l)))
      (f := g.as.unop) (g := Q))

set_option maxHeartbeats 800000 in
noncomputable def S3123FiberNatTransInvApp
    {a b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (g : a ⟶ b) (X : (S3123Right (l := l)).obj a) :
    ((S3123Right (l := l)).map g ≫ S3123FiberAppInv (l := l) b).toFunctor.obj X ⟶
      ((S3123FiberAppInv (l := l) a ≫ (S3123Left (l := l)).map g).toFunctor.obj X) := by
  rcases X with ⟨Q⟩
  apply Discrete.eqToHom
  simp only [CategoryTheory.Cat.Hom.comp_toFunctor, Functor.comp_obj,
    S3123Right_map_apply, S3123FiberAppInv_apply, S3123Left_map_apply]
  exact S3123FiberNatTransInv_app_eq (l := l) g Q

set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
noncomputable def S3123FiberNatTransInv
    {a b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ}
    (g : a ⟶ b) :
    ((S3123Right (l := l)).map g ≫ S3123FiberAppInv (l := l) b) ⟶
      (S3123FiberAppInv (l := l) a ≫ (S3123Left (l := l)).map g) :=
  { toNatTrans :=
    { app := fun X => S3123FiberNatTransInvApp (l := l) g X
      naturality := fun X Y f => Subsingleton.elim _ _ } }

#check S3123FiberNatTransInv
#check S3123FiberNatTransInvApp

end LeanFormal.IUT.XiFPaper.S3123FiberStrongTransInvActual
end
