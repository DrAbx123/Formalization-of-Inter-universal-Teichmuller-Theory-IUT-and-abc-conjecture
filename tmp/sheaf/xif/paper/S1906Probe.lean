import tmp.sheaf.xif.paper.S1361DivisionCriterionActual
import tmp.sheaf.xif.paper.S1894D5LargeImageActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1361DivisionCriterionActual
open LeanFormal.IUT.XiFPaper.S1329RankTwoTorsionBasisActual

abbrev S1906K : Type := AlgebraicClosure S1720Field
abbrev S1906W : WeierstrassCurve S1906K := S1720Curve.curve.baseChange S1906K

#check s1329NatCard_torsionBy_congr
#check s1329NatCard_torsionBy_eq
#check s1329NatCard_eq_sq_iff_separable
#check s1329RootFinset
#check s1329DivisionCriterion
#check s1329NoTwoTorsionRoots_of_criterion

end LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
