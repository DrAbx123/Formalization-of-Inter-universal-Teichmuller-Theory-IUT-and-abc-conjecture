import tmp.sheaf.xif.paper.S3123UnitIsoDataDirectActualAdapted
import tmp.sheaf.xif.paper.S3123UnitIsoDataActual
import tmp.sheaf.xif.paper.S3123FiberEquivalenceActual
import tmp.sheaf.xif.paper.S3123RightObjSubsingletonActual

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
open LeanFormal.IUT.XiFPaper.S3123UnitIsoDataActual
open LeanFormal.IUT.XiFPaper.S3123UnitIsoDataDirectActualAdapted
open LeanFormal.IUT.XiFPaper.S3123RightObjSubsingletonActual

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory
attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.homCategory

namespace LeanFormal.IUT.XiFPaper.S3123CounitIsoDataDirectActualAdapted

variable {l : PrimeGeFive}

set_option maxHeartbeats 800000 in
noncomputable def S3123CounitAppDirect
    (U : LocallyDiscrete (Iut.SchemeOverField (S1280Arithmetic l).K)ᵒᵖ) :
    (Pseudofunctor.StrongTrans.vcomp (S3123FiberStrongTransInv)
      (S3123FiberStrongTrans)).app U ≅
      (Pseudofunctor.StrongTrans.id (S3123Right (l := l))).app U := by
  rw [Pseudofunctor.StrongTrans.comp_app, Pseudofunctor.StrongTrans.comp_app]
  exact CategoryTheory.Cat.Hom.isoMk
    (NatIso.ofComponents
      (fun Q => by
        rcases Q with ⟨q⟩
        rw [Functor.id_obj, Functor.comp_obj]
        rw [S3123FiberAppInv_apply, S3123FiberApp_apply]
        exact S3123DiscreteIsoOfHom (Discrete.eqToHom (by
          exact (Equiv.symm_apply_apply _ q).symm)))
      (fun {X Y} f => by
        simp only [Functor.id_obj, Functor.comp_obj]
        exact Subsingleton.elim _ _))

set_option maxHeartbeats 800000 in
noncomputable def S3123CounitIsoDataDirect : S3123CounitIsoData (l := l) :=
  { app := fun U => S3123CounitAppDirect (l := l) U
    naturality := fun {U V} f => by
      exact Subsingleton.elim _ _ }

#check S3123CounitIsoDataDirect

end LeanFormal.IUT.XiFPaper.S3123CounitIsoDataDirectActualAdapted
end
