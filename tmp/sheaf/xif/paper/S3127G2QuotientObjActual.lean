import tmp.sheaf.xif.paper.S3127KLinearFullActual
import tmp.sheaf.xif.paper.S3127FreeQuotientActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveGaloisCategory
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2QuotientObjActual
variable {l : PrimeGeFive}

noncomputable def S3127G2QuotientObj
    (Q : FiniteEtaleCover (S1419AffineScheme l)) :
    S3127FiniteEtaleOverKFull l := by
  let QoverK := Over.mk (Q.obj.hom ≫ (S1419AffineOver l).hom)
  let f : QoverK ⟶ S1419AffineOver l :=
    Over.homMk Q.obj.hom (by dsimp [QoverK]; rfl)
  refine ⟨Over.mk f, ?_⟩
  exact ⟨Q.property.2, Q.property.1⟩

#check S3127G2QuotientObj
end LeanFormal.IUT.XiFPaper.S3127G2QuotientObjActual
end
