import tmp.sheaf.xif.paper.S3127KLinearFullActual
import tmp.sheaf.xif.paper.S3127FreeQuotientActual
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
import tmp.sheaf.xif.paper.S1348D6OrbicurveActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2FullCoverAffineConsumerActual
variable {l : PrimeGeFive}

theorem S3127G2FullCoverAffineConsumer (B : S3127FiniteEtaleOverKFull l) :
    IsAffine B.obj.left.left ∧ IsFinite B.obj.hom.left ∧ Etale B.obj.hom.left := by
  exact ⟨S3127FullCover_isAffine B, B.property.1, B.property.2⟩

#check S3127G2FullCoverAffineConsumer
end LeanFormal.IUT.XiFPaper.S3127G2FullCoverAffineConsumerActual
end
