import tmp.sheaf.xif.paper.S3123ObjEqActual

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

namespace LeanFormal.IUT.XiFPaper.S3123LeftCoeActual

variable {l : PrimeGeFive}

lemma S3123Left_obj_coe
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (↑((S3123Left (l := l)).obj U) : Type) =
      Discrete (Opposite.unop U.as ⟶ S3123BaseChangedScheme (l := l)) :=
  congrArg (fun C : Cat => (↑C : Type)) (S3123Left_obj_eq (l := l) U)

#check S3123Left_obj_coe

end LeanFormal.IUT.XiFPaper.S3123LeftCoeActual
end
