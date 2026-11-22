import tmp.sheaf.xif.paper.S3123LeftExplicit2Actual

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
open LeanFormal.IUT.XiFPaper.S3123LeftMapCompActual
open LeanFormal.IUT.XiFPaper.S3123LeftExplicit2Actual

namespace LeanFormal.IUT.XiFPaper.S3123UnitCompExplicitActual

variable {l : PrimeGeFive}

noncomputable def S3123FiberAppExplicit
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    S3123LeftObj (l := l) U ⟶ (S3123Right (l := l)).obj U :=
  (Discrete.functor (fun P : Opposite.unop U.as ⟶
      S3123BaseChangedScheme (l := l) =>
    Discrete.mk (((Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
      (Opposite.unop U.as) (S1419AffineOver (l := l))).symm P))).toCatHom

noncomputable def S3123FiberAppInvExplicit
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (S3123Right (l := l)).obj U ⟶ S3123LeftObj (l := l) U :=
  (Discrete.functor (fun Q : (Over.map (S3123BaseSpecMap (l := l))).obj
      (Opposite.unop U.as) ⟶ S1419AffineOver (l := l) =>
    Discrete.mk (((Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
      (Opposite.unop U.as) (S1419AffineOver (l := l))) Q))).toCatHom

@[simp] lemma S3123FiberAppExplicit_apply
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ)
    (P : Opposite.unop U.as ⟶ S3123BaseChangedScheme (l := l)) :
    (S3123FiberAppExplicit (l := l) U).toFunctor.obj (Discrete.mk P) =
      Discrete.mk (((Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
        (Opposite.unop U.as) (S1419AffineOver (l := l))).symm P) := rfl

@[simp] lemma S3123FiberAppInvExplicit_apply
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ)
    (Q : (Over.map (S3123BaseSpecMap (l := l))).obj (Opposite.unop U.as) ⟶
      S1419AffineOver (l := l)) :
    (S3123FiberAppInvExplicit (l := l) U).toFunctor.obj (Discrete.mk Q) =
      Discrete.mk (((Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
        (Opposite.unop U.as) (S1419AffineOver (l := l))) Q) := rfl

set_option maxHeartbeats 800000 in
noncomputable def S3123UnitCompExplicit
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ)
    (P : Opposite.unop U.as ⟶ S3123BaseChangedScheme (l := l)) :
    (Discrete.mk P : S3123LeftObj (l := l) U) ≅
      (S3123FiberAppInvExplicit (l := l) U).toFunctor.obj
        ((S3123FiberAppExplicit (l := l) U).toFunctor.obj (Discrete.mk P)) :=
  S3123DiscreteIsoOfHom (Discrete.eqToHom (by
    simp only [S3123FiberAppExplicit_apply, S3123FiberAppInvExplicit_apply]
    exact (Equiv.apply_symm_apply _ P).symm))

#check S3123UnitCompExplicit

end LeanFormal.IUT.XiFPaper.S3123UnitCompExplicitActual
end
