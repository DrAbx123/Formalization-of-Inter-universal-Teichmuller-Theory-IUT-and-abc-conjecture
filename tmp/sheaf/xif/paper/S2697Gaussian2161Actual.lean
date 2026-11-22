import tmp.sheaf.xif.paper.S2696VbadActual
import tmp.sheaf.xif.paper.S2687Split2161Actual
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2696VbadActual

namespace LeanFormal.IUT.XiFPaper.S2697Gaussian2161Actual

local instance s2697GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

theorem S2697_place2161_eq_S2687 :
    S2696Place2161 = S2687Place := rfl

theorem S2697_hasSplitMultiplicativeReductionAt2161 :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasSplitMultiplicativeReductionAt
      S2696GaussianPlace2161 := by
  refine PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_baseChange
    (X := concreteSplitPuncturedCurve) (place := S2696GaussianPlace2161) ?_
  rw [S2696GaussianPlace2161_comap, S2697_place2161_eq_S2687]
  exact S2687HasSplitMultiplicativeReductionAt2161

theorem S2697_hasMultiplicativeReductionAt2161 :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasMultiplicativeReductionAt
      S2696GaussianPlace2161 :=
  PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_imp_multiplicative
    S2697_hasSplitMultiplicativeReductionAt2161

#check S2697_hasSplitMultiplicativeReductionAt2161
#check S2697_hasMultiplicativeReductionAt2161
#print axioms S2697_hasSplitMultiplicativeReductionAt2161
#print axioms S2697_hasMultiplicativeReductionAt2161

end LeanFormal.IUT.XiFPaper.S2697Gaussian2161Actual
end
