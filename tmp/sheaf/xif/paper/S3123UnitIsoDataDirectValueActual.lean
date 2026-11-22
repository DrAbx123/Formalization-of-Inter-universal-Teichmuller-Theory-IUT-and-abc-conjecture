import tmp.sheaf.xif.paper.S3123UnitIsoDataDirectActual
import tmp.sheaf.xif.paper.S3123UnitIsoDataActual

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
open LeanFormal.IUT.XiFPaper.S3123LeftCoeActual
open LeanFormal.IUT.XiFPaper.S3123LeftExplicitActual
open LeanFormal.IUT.XiFPaper.S3123LeftObjSubsingletonActual
open LeanFormal.IUT.XiFPaper.S3123UnitCompExplicitActual
open LeanFormal.IUT.XiFPaper.S3123UnitIsoDataActual
open LeanFormal.IUT.XiFPaper.S3123UnitIsoDataDirectActual

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory
attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.homCategory

namespace LeanFormal.IUT.XiFPaper.S3123UnitIsoDataDirectValueActual

variable {l : PrimeGeFive}

set_option maxHeartbeats 800000 in
noncomputable def S3123UnitIsoDataDirect : S3123UnitIsoData (l := l) :=
  { app := fun U => S3123UnitAppDirect (l := l) U
    naturality := fun {U V} f => by
      exact Subsingleton.elim _ _ }

#check S3123UnitIsoDataDirect

end LeanFormal.IUT.XiFPaper.S3123UnitIsoDataDirectValueActual
end
