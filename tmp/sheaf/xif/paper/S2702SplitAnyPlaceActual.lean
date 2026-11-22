import tmp.sheaf.xif.paper.S2697Gaussian2161Actual
import tmp.sheaf.xif.paper.S2687Split2161Actual
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteFinitePlaceBoundary
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2696VbadActual
open LeanFormal.IUT.XiFPaper.S2697Gaussian2161Actual

namespace LeanFormal.IUT.XiFPaper.S2702SplitAnyPlaceActual

local instance s2702GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

theorem S2702_split_over_rational
    (q : NumberField.FinitePlace ℚ)
    (hX : concreteSplitPuncturedCurve.HasSplitMultiplicativeReductionAt q)
    (p : NumberField.FinitePlace GaussianField)
    (hp : NumberFieldFinitePlace.comap (k := ℚ) p = q) :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasSplitMultiplicativeReductionAt p := by
  refine PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_baseChange
    (X := concreteSplitPuncturedCurve) (place := p) ?_
  rw [hp]
  exact hX

theorem S2702_split_over_five
    (p : NumberField.FinitePlace GaussianField)
    (hp : NumberFieldFinitePlace.comap (k := ℚ) p = concreteFivePlace) :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasSplitMultiplicativeReductionAt p :=
  S2702_split_over_rational concreteFivePlace
    concreteSplitPuncturedCurve_hasSplitMultiplicativeReductionAt_five p hp

theorem S2702_split_over_2161
    (p : NumberField.FinitePlace GaussianField)
    (hp : NumberFieldFinitePlace.comap (k := ℚ) p = S2687Place) :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasSplitMultiplicativeReductionAt p :=
  S2702_split_over_rational S2687Place
    S2687HasSplitMultiplicativeReductionAt2161 p hp

theorem S2702_split_at_GaussianFivePlace :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasSplitMultiplicativeReductionAt
      concreteGaussianFivePlace :=
  S2702_split_over_five concreteGaussianFivePlace concreteGaussianFivePlace_comap

theorem S2702_split_at_S2696GaussianPlace :
    (concreteSplitPuncturedCurve.baseChange GaussianField).HasSplitMultiplicativeReductionAt
      S2696GaussianPlace2161 :=
  S2702_split_over_2161 S2696GaussianPlace2161 (by
    rw [S2696GaussianPlace2161_comap]
    exact S2697_place2161_eq_S2687)

#check S2702_split_over_rational
#check S2702_split_over_five
#check S2702_split_over_2161
#check S2702_split_at_GaussianFivePlace
#check S2702_split_at_S2696GaussianPlace
#print axioms S2702_split_over_rational
#print axioms S2702_split_at_GaussianFivePlace
#print axioms S2702_split_at_S2696GaussianPlace

end LeanFormal.IUT.XiFPaper.S2702SplitAnyPlaceActual
end
