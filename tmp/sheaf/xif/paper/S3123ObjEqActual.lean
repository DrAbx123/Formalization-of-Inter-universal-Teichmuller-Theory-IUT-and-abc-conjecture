import tmp.sheaf.xif.paper.S3123InvNatActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual

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

namespace LeanFormal.IUT.XiFPaper.S3123ObjEqActual

variable {l : PrimeGeFive}

lemma S3123Right_obj_eq
    (b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (S3123Right (l := l)).obj b =
      Cat.of (Discrete
        ((Over.map (S3123BaseSpecMap (l := l))).obj (Opposite.unop b.as) ⟶
          S1419AffineOver (l := l))) := by
  dsimp only [S3123Right, Pseudofunctor.comp, PrelaxFunctor.comp,
    PrelaxFunctorStruct.comp, Prefunctor.comp,
    schemeRestrictScalarsPseudofunctor, schemeRestrictScalars,
    S1536XF, S1742YS]
  rfl

lemma S3123Left_obj_eq
    (b : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (S3123Left (l := l)).obj b =
      Cat.of (Discrete
        (Opposite.unop b.as ⟶ S3123BaseChangedScheme (l := l))) := by
  dsimp only [S3123Left, Iut.schemeRepresentableEtalePseudofunctor]
  rfl

#check S3123Right_obj_eq
#check S3123Left_obj_eq

end LeanFormal.IUT.XiFPaper.S3123ObjEqActual
end
