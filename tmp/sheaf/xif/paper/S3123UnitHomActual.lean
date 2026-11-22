import tmp.sheaf.xif.paper.S3123UnitActual

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
open LeanFormal.IUT.XiFPaper.S3123UnitActual

namespace LeanFormal.IUT.XiFPaper.S3123UnitHomActual

variable {l : PrimeGeFive}

@[simp] lemma S3123UnitComp_hom
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ)
    (P : Opposite.unop U.as ⟶ S3123BaseChangedScheme (l := l)) :
    (S3123UnitComp (l := l) U P).hom =
      Discrete.eqToHom (by
        change P = ((Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
          (Opposite.unop U.as) (S1419AffineOver (l := l)))
            (((Over.mapPullbackAdj (S3123BaseSpecMap (l := l))).homEquiv
              (Opposite.unop U.as) (S1419AffineOver (l := l))).symm P)
        exact (Equiv.apply_symm_apply _ P).symm) := rfl

#check S3123UnitComp_hom

end LeanFormal.IUT.XiFPaper.S3123UnitHomActual
end
