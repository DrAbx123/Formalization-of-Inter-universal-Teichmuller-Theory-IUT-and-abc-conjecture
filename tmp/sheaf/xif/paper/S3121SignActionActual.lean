import tmp.sheaf.xif.paper.S3121SignDataAssembly
import tmp.sheaf.xif.paper.S2852OrbicurveSignActionCoherentActual

noncomputable section
open LeanFormal.IUT CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans Bicategory
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionOverActual
open LeanFormal.IUT.XiFPaper.S3121SignDataActual
open LeanFormal.IUT.XiFPaper.S3121DiagramActual
open LeanFormal.IUT.XiFPaper.S3121SignDataAssembly
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual

namespace LeanFormal.IUT.XiFPaper.S3121SignActionActual

variable {l : PrimeGeFive}

noncomputable def S3121SignActionActual :
    Iut.OrbicurveSignAction (S1536XF (l := l)) :=
  Iut.orbicurveSignActionOf (S1536XF (l := l))
    (S3121SignDataActual' (l := l)).D
    (S3121SignDataActual' (l := l)).atBase
    (S3119NegEllipticInvolution (l := l))
    (S3121SignDataActual' (l := l)).generator_identification
    (S3119NegEllipticInvolution_squared (l := l))

#check S3121SignActionActual
#print axioms S3121SignActionActual

end LeanFormal.IUT.XiFPaper.S3121SignActionActual
end
