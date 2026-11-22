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
namespace LeanFormal.IUT.XiFPaper.S3127G2FullCoverAffineDataActual
variable {l : PrimeGeFive}

structure S3127G2FullCoverAffineData (B : S3127FiniteEtaleOverKFull l) : Type where
  isAffine : IsAffine B.obj.left.left
  finite : IsFinite B.obj.hom.left
  etale : Etale B.obj.hom.left

noncomputable def S3127G2FullCoverAffineData.of
    (B : S3127FiniteEtaleOverKFull l) : S3127G2FullCoverAffineData B where
  isAffine := S3127FullCover_isAffine B
  finite := B.property.1
  etale := B.property.2

#check S3127G2FullCoverAffineData
#check S3127G2FullCoverAffineData.of
end LeanFormal.IUT.XiFPaper.S3127G2FullCoverAffineDataActual
end
