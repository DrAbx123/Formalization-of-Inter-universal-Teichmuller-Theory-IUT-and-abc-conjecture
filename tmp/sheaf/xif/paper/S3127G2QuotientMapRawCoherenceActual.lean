import tmp.sheaf.xif.paper.S3127G2QuotientMapActual
import tmp.sheaf.xif.paper.S3127G2QuotientMapRawActual
import tmp.sheaf.xif.paper.S3127FullForgetActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FreeQuotientActual
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapActualFull
open LeanFormal.IUT.XiFPaper.S3127G2QuotientMapRawActual
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
open LeanFormal.IUT.XiFPaper.S3127G2RActionActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127G2QuotientMapRawCoherenceActual
variable {l : PrimeGeFive} {G : Type} [Group G]
variable (A : S3127FiniteEtaleOverKFull l) (act : S3127OverRAction A G)
variable [Fintype G] [DecidableEq G]

theorem S3127FullForget_map_quotientMap :
    (S3127FullForget (l := l)).map (S3127G2QuotientMap A act) =
      S3127G2QuotientMapRaw A act := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  rfl

#check S3127FullForget_map_quotientMap
end LeanFormal.IUT.XiFPaper.S3127G2QuotientMapRawCoherenceActual
end
