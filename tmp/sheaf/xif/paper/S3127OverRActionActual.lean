import tmp.sheaf.xif.paper.S3127KLinearFullActual

noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S3127OverRActionActual
variable {l : PrimeGeFive} {G : Type} [Group G]

/-- An action on the underlying scheme of a full finite etale cover, over R. -/
structure S3127OverRAction
    (A : S3127FiniteEtaleOverKFull l) (G : Type) [Group G] where
  act : G →* Aut A.obj.left.left
  overR : ∀ g : G, (act g).hom ≫ A.obj.hom.left = A.obj.hom.left

#check S3127OverRAction
end LeanFormal.IUT.XiFPaper.S3127OverRActionActual
end