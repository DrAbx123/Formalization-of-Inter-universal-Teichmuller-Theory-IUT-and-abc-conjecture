import tmp.sheaf.xif.paper.S3127KLinearFullActual
import tmp.sheaf.xif.paper.S3127FreeQuotientActual
import tmp.sheaf.xif.paper.S3127GammaRAlgebraActual
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127GammaRAlgebraActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2AlgebraBridgeConsumerActual
variable {l : PrimeGeFive}

structure S3127G2AlgebraBridgeConsumer (B : S3127FiniteEtaleOverKFull l) : Type where
  algebra : Algebra (S1348CoordinateRing l) (Scheme.Γ.obj (Opposite.op B.obj.left.left))
  etale : letI := algebra; Algebra.Etale (S1348CoordinateRing l)
    (Scheme.Γ.obj (Opposite.op B.obj.left.left))
  finite : letI := algebra; Module.Finite (S1348CoordinateRing l)
    (Scheme.Γ.obj (Opposite.op B.obj.left.left))

noncomputable def S3127G2AlgebraBridgeConsumer.of
    (B : S3127FiniteEtaleOverKFull l) :
    S3127G2AlgebraBridgeConsumer B := by
  let R := S1348CoordinateRing l
  let Y := B.obj.left.left
  let hom := B.obj.hom.left
  letI := gammaAlgebraOf Y hom
  exact {
    algebra := inferInstance
    etale := gammaEtaleOf Y hom B.property.2 (by rfl)
    finite := gammaFiniteOf Y hom B.property.1 (by rfl) }

#check S3127G2AlgebraBridgeConsumer
#check S3127G2AlgebraBridgeConsumer.of
end LeanFormal.IUT.XiFPaper.S3127G2AlgebraBridgeConsumerActual
end
