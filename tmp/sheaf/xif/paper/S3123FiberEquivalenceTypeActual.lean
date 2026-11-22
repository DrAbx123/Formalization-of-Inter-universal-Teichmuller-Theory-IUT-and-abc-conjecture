import tmp.sheaf.xif.paper.S3123XKStackExtension

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

namespace LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceTypeActual

variable {l : PrimeGeFive}
variable [Bicategory (Iut.EtaleStackPseudofunctor (S1280Arithmetic l).K)]

abbrev S3123FiberEquivalenceType : Type :=
  Bicategory.Equivalence (S3123Result (l := l)).fiber
    (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor
      (S1280Arithmetic l).F (S1280Arithmetic l).K)
      (S1536XF (l := l)).stack.fiber)

#check S3123FiberEquivalenceType

end LeanFormal.IUT.XiFPaper.S3123FiberEquivalenceTypeActual
end
