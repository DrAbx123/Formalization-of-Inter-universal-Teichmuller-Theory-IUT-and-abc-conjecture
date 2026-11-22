import tmp.sheaf.xif.paper.S3123ObjEqActual
import tmp.sheaf.xif.paper.S3123RightCoeActual

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
open LeanFormal.IUT.XiFPaper.S3123ObjEqActual
open LeanFormal.IUT.XiFPaper.S3123RightCoeActual

namespace LeanFormal.IUT.XiFPaper.S3123RightObjSubsingletonActual

variable {l : PrimeGeFive}

set_option maxHeartbeats 800000 in
instance S3123RightObjHomSubsingleton
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ)
    (X Y : (S3123Right (l := l)).obj U) :
    Subsingleton (X ⟶ Y) := by
  let I := ((Over.map (S3123BaseSpecMap (l := l))).obj (Opposite.unop U.as) ⟶
    S1419AffineOver (l := l))
  let hcat : (S3123Right (l := l)).obj U = Cat.of (Discrete I) :=
    S3123Right_obj_eq (l := l) U
  let X' : Cat.of (Discrete I) := hcat ▸ X
  let Y' : Cat.of (Discrete I) := hcat ▸ Y
  have h : Subsingleton (X' ⟶ Y') :=
    S3123FiberNatTransActual.S3123DiscreteHomSubsingleton _ _ _
  refine Eq.rec (motive := fun (C : Cat) (hC : (S3123Right (l := l)).obj U = C) =>
    Subsingleton ((hC ▸ X) ⟶ (hC ▸ Y))) h hcat

#check S3123RightObjHomSubsingleton

end LeanFormal.IUT.XiFPaper.S3123RightObjSubsingletonActual
end
