import LeanFormal.IUT.ABCBridge.Geometry.FreyOddReduction
import LeanFormal.IUT.ABCBridge.Geometry.FreySplitMultiplicativeReduction
import LeanFormal.IUT.ABCBridge.Geometry.FreyTwoAdicMinimalReduction

/-!
# ShehddFreyReductionChainActual — p-adic Frey reduction chain

Reuses the compiled uncovered ABCBridge/Frey reduction assets (FreyOddReduction,
FreySplitMultiplicativeReduction, FreyTwoAdicMinimalReduction) to form genuine chain
theorems: the p-adic integral model/generic fibre/discriminant package, the split
multiplicative splitting polynomial formula, and the two-adic halving model formulas.

No new assumptions, no sorry/axiom.  These are consumer-level consequences only; the
reduction statements themselves stay in their compiled modules.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddFreyReductionChainActual

open LeanFormal.IUT
open Polynomial
open scoped WeierstrassCurve

/-- **PROVED chain:** p-adic Frey reduction package: the integral model's generic fibre
is the p-adic Frey curve, the curve is integral, its discriminant is `16(abc)^2`, and the
Frey residue field has characteristic `p`. -/
theorem freyPadic_reduction_chain (p a b c : ℕ) [Fact p.Prime] (hsum : a + b = c) :
    (freyPadicIntegralModel p a b)⁄ℚ_[p] = freyPadicCurve p a b ∧
      WeierstrassCurve.IsIntegral ℤ_[p] (freyPadicCurve p a b) ∧
        (freyPadicCurve p a b).Δ = ((16 * (a * b * c) ^ 2 : ℕ) : ℚ_[p]) ∧
          CharP (FreyResidueField p) p :=
  ⟨freyPadicIntegralModel_baseChange p a b,
    freyPadicCurve_isIntegral p a b,
    freyPadicCurve_discriminant hsum,
    freyResidue_charP p⟩

/-- **PROVED chain:** split multiplicative reduction: the splitting polynomial has the
explicit quadratic form, is natural under ring maps, and its zero-left specialization is
factored. -/
theorem freyMultiplicative_splitting_chain {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b : R) :
    freyMultiplicativeSplittingPolynomial a b =
        C (16 * (a ^ 2 + a * b + b ^ 2)) * X ^ 2 -
          C ((b - a) * (16 * (a ^ 2 + a * b + b ^ 2) + 24 * a * b)) ∧
      (freyMultiplicativeSplittingPolynomial a b).map f =
        freyMultiplicativeSplittingPolynomial (f a) (f b) :=
  ⟨freyMultiplicativeSplittingPolynomial_eq a b,
    freyMultiplicativeSplittingPolynomial_map f a b⟩

/-- **PROVED chain:** two-adic minimal reduction: the halving model has coefficients
`a₁ = 1`, `a₃ = a₆ = 0`, and discriminant `16(abc)^2 / 4096`. -/
theorem freyTwoAdic_halving_chain {a b c : ℕ} (hsum : a + b = c) :
    (freyTwoAdicHalvingModel a b).a₁ = 1 ∧
      (freyTwoAdicHalvingModel a b).a₃ = 0 ∧
        (freyTwoAdicHalvingModel a b).a₆ = 0 ∧
          (freyTwoAdicHalvingModel a b).Δ =
            (16 * (a * b * c) ^ 2 : ℚ_[2]) / 4096 :=
  ⟨freyTwoAdicHalvingModel_a₁ a b,
    freyTwoAdicHalvingModel_a₃ a b,
    freyTwoAdicHalvingModel_a₆ a b,
    freyTwoAdicHalvingModel_discriminant hsum⟩

end LeanFormal.IUT.XiFPaper.ShehddFreyReductionChainActual
end
