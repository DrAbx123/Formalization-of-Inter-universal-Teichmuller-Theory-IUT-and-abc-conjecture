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
set_option maxHeartbeats 16000000
namespace LeanFormal.IUT.XiFPaper.S3123FiberInvActual
variable {l : PrimeGeFive}
noncomputable def S3123FiberAppInv
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (S3123Right (l := l)).obj U ⟶ (S3123Left (l := l)).obj U :=
  (Discrete.functor (fun Q : (schemeRestrictScalars
      (S1280Arithmetic l).F (S1280Arithmetic l).K).obj (Opposite.unop U.as) ⟶
      S1419AffineOver (l := l) =>
    Discrete.mk ((Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
      (Opposite.unop U.as) (S1419AffineOver (l := l)) Q))).toCatHom
lemma S3123FiberAppInv_apply
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ)
    (Q : (schemeRestrictScalars (S1280Arithmetic l).F
      (S1280Arithmetic l).K).obj (Opposite.unop U.as) ⟶ S1419AffineOver (l := l)) :
    (S3123FiberAppInv (l := l) U).toFunctor.obj (Discrete.mk Q) =
      Discrete.mk ((Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
        (Opposite.unop U.as) (S1419AffineOver (l := l)) Q) := rfl
lemma S3123Comp_toFunctor_obj {C D E : Cat} (G : C ⟶ D) (H : D ⟶ E) (X : C) :
    (G ≫ H).toFunctor.obj X = H.toFunctor.obj (G.toFunctor.obj X) := rfl
noncomputable def S3123FiberInvNat
    {a b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ} (g : a ⟶ b) :
    (S3123Right (l := l)).map g ≫ S3123FiberAppInv (l := l) b ≅
      S3123FiberAppInv (l := l) a ≫ (S3123Left (l := l)).map g := by
  apply eqToIso
  apply CategoryTheory.Cat.ext
  apply CategoryTheory.Discrete.functor_ext
  intro Q
  rw [S3123Comp_toFunctor_obj, S3123Comp_toFunctor_obj]
  rw [S3123Right_map_apply]
  change (S3123FiberAppInv (l := l) b).toFunctor.obj
      (Discrete.mk ((schemeRestrictScalars (S1280Arithmetic l).F
        (S1280Arithmetic l).K).map g.as.unop ≫ Q)) =
    ((S3123Left (l := l)).map g).toFunctor.obj
      (Discrete.mk ((Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
        (Opposite.unop a.as) (S1419AffineOver (l := l)) Q))
  rw [S3123FiberAppInv_apply]
  rw [S3123Left_map_apply]
  apply CategoryTheory.Discrete.ext
  exact CategoryTheory.Adjunction.homEquiv_naturality_left _ g.as.unop Q
#check S3123FiberAppInv
#check S3123FiberInvNat
end LeanFormal.IUT.XiFPaper.S3123FiberInvActual
end
