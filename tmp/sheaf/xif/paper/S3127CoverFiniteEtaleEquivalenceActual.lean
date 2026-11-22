import tmp.sheaf.xif.paper.S3127ForgetfulActual
import tmp.sheaf.xif.paper.S3127KLinearFullActual
import tmp.sheaf.xif.paper.S3127FullForgetActual
import tmp.sheaf.xif.paper.RepresentableCoverChosenCategoryActual
import tmp.sheaf.xif.paper.S1419D6NonterminalStackActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3127ForgetfulActual
open LeanFormal.IUT.XiFPaper.S3127KLinearFullActual
open LeanFormal.IUT.XiFPaper.S3127FullForgetActual
open LeanFormal.IUT.XiFPaper.RepresentableCoverChosenCategoryActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3127CoverFiniteEtaleEquivalenceActual
variable {l : PrimeGeFive}

noncomputable def S3127CoverFiniteEtaleEquivalence :
    S3127Cover (l := l) ≌ FiniteEtaleCover (S1419AffineScheme l) :=
  (S3127KLinearEquivalence (l := l)).trans
    ((S3127OldNewEquivalence (l := l)).trans
      (S3127FullEquivalence (l := l)))

#check S3127CoverFiniteEtaleEquivalence
end LeanFormal.IUT.XiFPaper.S3127CoverFiniteEtaleEquivalenceActual
end
