import tmp.sheaf.xif.paper.S3123UnitIsoDataActual

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
open LeanFormal.IUT.XiFPaper.S3123StrongInvActual
open LeanFormal.IUT.XiFPaper.S3123UnitIsoDataActual

namespace LeanFormal.IUT.XiFPaper.S3123UnitIsoDataProjectionActual

variable {l : PrimeGeFive}

@[simp] lemma S3123UnitIsoData.toIso_hom_app
    (d : S3123UnitIsoData (l := l))
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (d.toIso).hom.as.app U = (d.app U).hom := rfl

@[simp] lemma S3123UnitIsoData.toIso_inv_app
    (d : S3123UnitIsoData (l := l))
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (d.toIso).inv.as.app U = (d.app U).inv := rfl

@[simp] lemma S3123CounitIsoData.toIso_hom_app
    (d : S3123CounitIsoData (l := l))
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (d.toIso).hom.as.app U = (d.app U).hom := rfl

@[simp] lemma S3123CounitIsoData.toIso_inv_app
    (d : S3123CounitIsoData (l := l))
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (d.toIso).inv.as.app U = (d.app U).inv := rfl

#check S3123UnitIsoData.toIso_hom_app
#check S3123CounitIsoData.toIso_hom_app

end LeanFormal.IUT.XiFPaper.S3123UnitIsoDataProjectionActual
end
