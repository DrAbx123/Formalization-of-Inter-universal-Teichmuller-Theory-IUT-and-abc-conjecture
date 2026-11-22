import tmp.sheaf.xif.paper.S3123UnitActual
import tmp.sheaf.xif.paper.S3123StrongTransVcompEqActual
import tmp.sheaf.xif.paper.S3123UnitIsoDataActual
import tmp.sheaf.xif.paper.S3123LeftObjSubsingletonActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Bicategory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open scoped Pseudofunctor.StrongTrans
open CategoryTheory.Pseudofunctor.StrongTrans
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
open LeanFormal.IUT.XiFPaper.S3123UnitActual
open LeanFormal.IUT.XiFPaper.S3123StrongTransVcompEqActual
open LeanFormal.IUT.XiFPaper.S3123LeftObjSubsingletonActual
open LeanFormal.IUT.XiFPaper.S3123UnitIsoDataActual

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory
attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.homCategory

namespace LeanFormal.IUT.XiFPaper.S3123UnitIsoDataDirectActual

variable {l : PrimeGeFive}

set_option maxHeartbeats 800000 in
noncomputable def S3123UnitAppOldComp
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (Pseudofunctor.StrongTrans.id (S3123Result (l := l)).fiber).app U ≅
      (S3123FiberApp (l := l) U ≫ S3123FiberAppInv (l := l) U) := by
  exact CategoryTheory.Cat.Hom.isoMk
    (NatIso.ofComponents
      (fun P => by
        rcases P with ⟨p⟩
        exact S3123UnitComp (l := l) U p)
      (fun {X Y} f => by
        exact Subsingleton.elim _ _))

set_option maxHeartbeats 800000 in
noncomputable def S3123UnitAppDirect
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (Pseudofunctor.StrongTrans.id (S3123Result (l := l)).fiber).app U ≅
      (Pseudofunctor.StrongTrans.vcomp (S3123FiberStrongTrans)
        (S3123FiberStrongTransInv)).app U := by
  exact (S3123UnitAppOldComp (l := l) U).trans
    (CategoryTheory.eqToIso (S3123FiberStrongTrans_vcomp_app (l := l) U).symm)

#check S3123UnitAppDirect

end LeanFormal.IUT.XiFPaper.S3123UnitIsoDataDirectActual
end
