import tmp.sheaf.xif.paper.S2690TwoPlaceBadQActual
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2690TwoPlaceBadQActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2748RationalAbsNormActual

/-- The absolute norm of the maximal ideal of the rational finite place at a
prime `p` is exactly `p`. -/
theorem S2748_absNorm_rationalFinitePlace (p : Nat) [Fact (Nat.Prime p)] :
    Ideal.absNorm (rationalFinitePlace p).maximalIdeal.asIdeal = p :=
  absNorm_rationalFinitePlace p

/-- comap of finite places gives the actual `LiesOver` relation on their
maximal ideals. -/
theorem S2748_liesOver_of_comap
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (P : NumberField.FinitePlace K) (p : NumberField.FinitePlace ℚ)
    (h : comap (k := ℚ) P = p) :
    P.maximalIdeal.asIdeal.LiesOver p.maximalIdeal.asIdeal := by
  rw [Ideal.liesOver_iff, Ideal.under_def]
  have hmax := NumberFieldFinitePlace.comap_maximalIdeal
    (k := ℚ) (K := K) P
  rw [h] at hmax
  exact hmax

/-- The same bridge in the form `P.maximalIdeal.asIdeal.LiesOver (span {(p:ℤ)})`
for a rational finite place. -/
theorem S2748_liesOver_span_of_comap
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (P : NumberField.FinitePlace K) (q : Nat) [Fact (Nat.Prime q)]
    (h : comap (k := ℚ) P = rationalFinitePlace q) :
    P.maximalIdeal.asIdeal.LiesOver (rationalFinitePlace q).maximalIdeal.asIdeal :=
  S2748_liesOver_of_comap P (rationalFinitePlace q) h

#check S2748_absNorm_rationalFinitePlace
#check S2748_liesOver_of_comap
#print axioms S2748_liesOver_of_comap

end LeanFormal.IUT.XiFPaper.S2748RationalAbsNormActual
end
