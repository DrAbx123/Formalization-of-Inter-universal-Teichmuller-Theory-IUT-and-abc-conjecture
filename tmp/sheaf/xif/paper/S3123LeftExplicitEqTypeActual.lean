import tmp.sheaf.xif.paper.S3123LeftExplicit2Actual

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
open LeanFormal.IUT.XiFPaper.S3123LeftCoeActual
open LeanFormal.IUT.XiFPaper.S3123LeftExplicitActual
open LeanFormal.IUT.XiFPaper.S3123LeftMapActual
open LeanFormal.IUT.XiFPaper.S3123LeftMapIdActual
open LeanFormal.IUT.XiFPaper.S3123LeftMapCompActual
open LeanFormal.IUT.XiFPaper.S3123LeftExplicit2Actual

namespace LeanFormal.IUT.XiFPaper.S3123LeftExplicitEqTypeActual

variable {l : PrimeGeFive}

abbrev S3123LeftExplicitEqType : Prop :=
  S3123LeftExplicit (l := l) = S3123Left (l := l)

#check S3123LeftExplicitEqType

end LeanFormal.IUT.XiFPaper.S3123LeftExplicitEqTypeActual
end
