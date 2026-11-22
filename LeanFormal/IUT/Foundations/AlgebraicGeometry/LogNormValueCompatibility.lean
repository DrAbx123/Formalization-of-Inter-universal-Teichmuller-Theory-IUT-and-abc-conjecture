import LeanFormal.IUT.IUTII.Frobenioid.Example36LogShellLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

/-!
# Actual completion uniformizer/log-normalization audit (L0.4 A/C)

Scratch audit.  The actual source term available in the tree is the production
completion uniformizer `adicCompletion_uniformizer` at
`concretePlace.maximalIdeal`; its completed valuation is `WithZero.exp (-1)`
and it is nonzero, hence lies in the maximal ideal (value `< 1`).

The actual analytic logarithm constructed in the tree is only the p-adic
`log1p` on principal units (`principalUnitLog`, `principalUnitLogImage`,
`integralLogShell`).  There is no actual definition or formula for `log(π)` on
a uniformizer, and no actual source normalization value for it.  The frozen
card `LogExtensionNormalizationCard` therefore cannot be inhabited by a real
source object; no production theorem consumes it.  No wrapper inhabitant is
constructed here.

Precise remaining source terms: (a) an actual completion uniformizer (available
below from production); (b) the source normalization value for `log(π)`, a
convention not determined by `log1p` on principal units; (c) the DVR
decomposition and the extension law of the logarithm to all of `K^x`;
(d) compatibility with the actual `unitLog` and multiplicativity on the source
unit group.  Only (a) is actual in the tree.
-/

noncomputable section

namespace LeanFormal.IUT.LogNormValueCompatibility

open scoped WithZero Valued
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge

universe u

local instance gaussianLogNormIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
/-! ## 1. The actual completion uniformizer -/

/-- The actual production uniformizer of the completed valuation at the
concrete Gaussian place, as an element of the actual local field
`concreteLogShellField = NormalizedCompletion concretePlace`. -/
noncomputable def concreteAdicUniformizer :
    concretePlace.maximalIdeal.adicCompletion GaussianField :=
  ((LeanFormal.IUT.NumberFieldFinitePlace.adicCompletion_uniformizer
      (K := GaussianField) concretePlace.maximalIdeal).1 :
    concretePlace.maximalIdeal.adicCompletion GaussianField)

/-- The actual uniformizer has value `exp(-1)` in the completed valuation. -/
theorem concreteAdicUniformizer_valued :
    (Valued.v (concreteAdicUniformizer) : WithZero (Multiplicative ℤ)) =
      WithZero.exp (-1 : ℤ) := by
  simpa [concreteAdicUniformizer] using
    LeanFormal.IUT.NumberFieldFinitePlace.uniformizer_valued_eq_exp_neg_one
      (K := GaussianField) (v := concretePlace.maximalIdeal)
      (LeanFormal.IUT.NumberFieldFinitePlace.adicCompletion_uniformizer
        (K := GaussianField) concretePlace.maximalIdeal)

/-- The actual uniformizer is nonzero. -/
theorem concreteAdicUniformizer_ne_zero : concreteAdicUniformizer ≠ 0 := by
  have h := (LeanFormal.IUT.NumberFieldFinitePlace.adicCompletion_uniformizer
    (K := GaussianField) concretePlace.maximalIdeal).ne_zero
  simpa [concreteAdicUniformizer] using h

/-- The actual uniformizer lies in the maximal ideal (value `< 1`). -/
theorem concreteAdicUniformizer_valued_lt_one :
    (Valued.v (concreteAdicUniformizer) : WithZero (Multiplicative ℤ)) < 1 := by
  rw [concreteAdicUniformizer_valued]
  exact LeanFormal.IUT.NumberFieldFinitePlace.withZero_exp_neg_one_lt_one

/-! ## 2. Available actual canonical log-norm term -/

/-- The actual canonical completion log-norm formula available in the tree:
for every nonzero element of the completed valuation, the logarithm of the
canonical norm is the valuation exponent times `log absNorm`. -/
theorem canonicalLogNorm_available
    (x : concretePlace.maximalIdeal.adicCompletion GaussianField) (hx : x ≠ 0) :
    Real.log ‖x‖ =
      (Multiplicative.toAdd (WithZero.unzero
        (LeanFormal.IUT.NumberFieldFinitePlace.valuation_ne_zero_of_ne_zero
          concretePlace x hx))) *
        Real.log (Ideal.absNorm concretePlace.maximalIdeal.asIdeal : ℝ) :=
  LeanFormal.IUT.NumberFieldFinitePlace.logNorm_eq_absNorm_mul
    concretePlace x hx

end LeanFormal.IUT.LogNormValueCompatibility

end