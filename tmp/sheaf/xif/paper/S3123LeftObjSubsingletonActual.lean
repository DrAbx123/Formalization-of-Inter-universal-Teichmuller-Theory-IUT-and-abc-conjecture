import tmp.sheaf.xif.paper.S3123UnitHomActual
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
open LeanFormal.IUT.XiFPaper.S3123ObjEqActual
open LeanFormal.IUT.XiFPaper.S3123LeftCoeActual
open LeanFormal.IUT.XiFPaper.S3123UnitActual
open LeanFormal.IUT.XiFPaper.S3123UnitHomActual

namespace LeanFormal.IUT.XiFPaper.S3123LeftObjSubsingletonActual

variable {l : PrimeGeFive}

set_option maxHeartbeats 800000 in
instance S3123LeftObjHomSubsingleton
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ)
    (X Y : (S3123Left (l := l)).obj U) :
    Subsingleton (X ⟶ Y) := by
  let I := (Opposite.unop U.as ⟶ S3123BaseChangedScheme (l := l))
  let hcat : (S3123Left (l := l)).obj U = Cat.of (Discrete I) :=
    S3123Left_obj_eq (l := l) U
  let X' : Cat.of (Discrete I) := hcat ▸ X
  let Y' : Cat.of (Discrete I) := hcat ▸ Y
  have h : Subsingleton (X' ⟶ Y') :=
    S3123FiberNatTransActual.S3123DiscreteHomSubsingleton _ _ _
  refine Eq.rec (motive := fun (C : Cat) (hC : (S3123Left (l := l)).obj U = C) =>
    Subsingleton ((hC ▸ X) ⟶ (hC ▸ Y))) h hcat

#check S3123LeftObjHomSubsingleton

end LeanFormal.IUT.XiFPaper.S3123LeftObjSubsingletonActual
end
