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

#check S3123FiberAppInv_apply


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

end LeanFormal.IUT.XiFPaper.S3123FiberStrongTransInvActual
end
