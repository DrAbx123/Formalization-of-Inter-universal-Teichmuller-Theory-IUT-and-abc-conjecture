import tmp.sheaf.xif.paper.S3123StrongInvActual

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
open LeanFormal.IUT.XiFPaper.S3123StrongInvActual

namespace LeanFormal.IUT.XiFPaper.S3123UnitActual

variable {l : PrimeGeFive}

set_option maxHeartbeats 800000 in
noncomputable def S3123UnitComp
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ)
    (P : Opposite.unop U.as ⟶ S3123BaseChangedScheme (l := l)) :
    (Discrete.mk P : (S3123Left (l := l)).obj U) ≅
      (S3123FiberAppInv (l := l) U).toFunctor.obj
        ((S3123FiberApp (l := l) U).toFunctor.obj (Discrete.mk P)) :=
  S3123DiscreteIsoOfHom (Discrete.eqToHom (by
    change P = ((Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
      (Opposite.unop U.as) (S1419AffineOver (l := l)))
        (((Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
          (Opposite.unop U.as) (S1419AffineOver (l := l))).symm P)
    exact (Equiv.apply_symm_apply _ P).symm))

#check S3123UnitComp

end LeanFormal.IUT.XiFPaper.S3123UnitActual
end
