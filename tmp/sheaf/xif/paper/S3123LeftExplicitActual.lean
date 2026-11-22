import tmp.sheaf.xif.paper.S3123LeftCoeActual

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
open LeanFormal.IUT.XiFPaper.S3123LeftCoeActual

namespace LeanFormal.IUT.XiFPaper.S3123LeftExplicitActual

variable {l : PrimeGeFive}

noncomputable def S3123LeftObj
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) : Cat :=
  Cat.of (Discrete (Opposite.unop U.as ⟶ S3123BaseChangedScheme (l := l)))

lemma S3123LeftObj_eq
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    S3123LeftObj (l := l) U = (S3123Left (l := l)).obj U :=
  (S3123Left_obj_eq (l := l) U).symm

#check S3123LeftObj
#check S3123LeftObj_eq

end LeanFormal.IUT.XiFPaper.S3123LeftExplicitActual
end
