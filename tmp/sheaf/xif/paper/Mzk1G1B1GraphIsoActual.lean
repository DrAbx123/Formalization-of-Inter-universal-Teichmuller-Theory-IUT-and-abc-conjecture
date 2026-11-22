/-
# B1 — the away/quotient dictionary: `C[Z]/(gZ − 1) ≃ C[1/g]` (P1) and its `λ`-side dual (P3)

Consumer: the graph-isomorphism lane of the smooth ↔ derivative criterion, route (b):
`Mzk1G1B1SmoothCriterionSubmActual.GraphIso h` (the missing ingredient of
`smoothAt_of_derivative_notMem`), whose first factor is exactly the standard isomorphism
`C[Z]/(gZ − 1) ≅ C[1/g]` of this file (there with `C = ℚ[λ]`, `g` the derivative).

## What is proved here (P1, P3; no sorry, no admit, no new axiom)

* `away_algEquiv_quotient`: for any commutative ring `C` and `g : C`,
    `C[Z]/(g·Z − 1) ≃ₐ[C] C[1/g]`.
  No work is needed beyond Mathlib's `Localization.awayEquivAdjoin`, because
  `AdjoinRoot f` *is* the quotient `C[X] ⧸ Ideal.span {f}` (definitionally, see
  `Mathlib.RingTheory.AdjoinRoot`), and `awayEquivAdjoin g : C[1/g] ≃ₐ[C] AdjoinRoot (C g * X - 1)`.
  We restate it in quotient form because that is the shape in which it is consumed by the
  ideal bookkeeping of `GraphIso h`.
* `graphIso_lambda_side`: the `λ`-side instance `C = ℚ[λ]` of P1, i.e.
  `ℚ[λ][Z]/(q·Z − 1) ≃ₐ[ℚ[λ]] ℚ[λ][1/q]`, obtained by specialising P1.
* `isLocalization_away_quotient`: the same statement in `IsLocalization` form,
  `IsLocalization.Away g (C[Z]/(g·Z − 1))`, which is the form quotient-elimination bookkeeping needs.
* `away_algEquiv_quotient_of_chartT`: the instance `C = ℚ[t]` (`= MvPolynomial (Fin 1) ℚ`,
  the renamed t-line of `Mzk1G1B1SmoothCriterionSubmActual.chartT`) of P1, i.e. the second factor
  of the graph isomorphism in the form needed there (`g = h'(t)`).

## Status of the lane

P1/P3 are unconditional.  P2 (`GraphIso h` itself, i.e. the full
`smoothModelRing h ≃ₐ[ℚ[λ]] ℚ[t][1/h']`) is *not* claimed here; it needs the exactness of the
two relations (`ker = span`) together with the rearrangement `ℚ[λ][T,Z] ≅ ℚ[T][λ,Z]`, which is
separate work.
-/
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.MvPolynomial.Basic

noncomputable section
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

open Polynomial

namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1GraphIsoActual

/-! ## P1: `C[Z]/(g·Z − 1) ≃ₐ[C] C[1/g]` -/

/-- **P1.** For a commutative ring `C` and `g : C`, the quotient of `C[Z]` by `g·Z − 1` is the
localization of `C` away from `g`.

Mathlib proves this as `Localization.awayEquivAdjoin g : C[1/g] ≃ₐ[C] AdjoinRoot (C g * X - 1)`,
and `AdjoinRoot (C g * X - 1)` is by definition the quotient `C[X] ⧸ Ideal.span {C g * X - 1}`;
we only state the result in the quotient shape consumed by the graph-isomorphism bookkeeping. -/
theorem away_algEquiv_quotient (C : Type) [CommRing C] (g : C) :
    Nonempty ((Polynomial C ⧸ Ideal.span {Polynomial.C g * Polynomial.X - 1}) ≃ₐ[C]
      Localization.Away g) :=
  ⟨(Localization.awayEquivAdjoin g).symm⟩

/-! ## P3: the `λ`-side dual, `C = ℚ[λ]` -/

/-- **P3.** The `λ`-side dual of P1: for `q ∈ ℚ[λ]`,
`ℚ[λ][Z]/(q·Z − 1) ≃ₐ[ℚ[λ]] ℚ[λ][1/q]`.  Direct specialisation of `away_algEquiv_quotient`. -/
theorem graphIso_lambda_side (q : Polynomial ℚ) :
    Nonempty ((Polynomial (Polynomial ℚ) ⧸
        Ideal.span {Polynomial.C q * Polynomial.X - 1}) ≃ₐ[Polynomial ℚ]
      Localization.Away q) :=
  away_algEquiv_quotient (Polynomial ℚ) q

/-! ## The `IsLocalization` form (the shape P2's bookkeeping consumes) -/

/-- **P1, localization form.** The quotient `C[Z]/(g·Z − 1)` *is* the localization of `C` away from `g`
(not merely isomorphic to it): `IsLocalization.Away g (C[Z]/(g·Z − 1))`.

This is Mathlib's `IsLocalization.adjoin_inv g` rewritten through the definitional identity
`AdjoinRoot f = C[X] ⧸ Ideal.span {f}`; it is the form needed when the `C[Z]/(gZ − 1)` factor of the
graph isomorphism has to be fed to `IsLocalization.lift`/`IsLocalization.algEquiv` inside a
quotient-elimination step. -/
theorem isLocalization_away_quotient (C : Type) [CommRing C] (g : C) :
    IsLocalization.Away g (Polynomial C ⧸ Ideal.span {Polynomial.C g * Polynomial.X - 1}) :=
  IsLocalization.adjoin_inv g

/-- The localization form of the `C = ℚ[t]` instance of P1. -/
theorem isLocalization_away_quotient_of_chartT (g : MvPolynomial (Fin 1) ℚ) :
    IsLocalization.Away g
      (Polynomial (MvPolynomial (Fin 1) ℚ) ⧸
        Ideal.span {Polynomial.C g * Polynomial.X - 1}) :=
  isLocalization_away_quotient (MvPolynomial (Fin 1) ℚ) g

/-! ## The `C = ℚ[t]` instance (second factor of the graph isomorphism) -/

/-- The `C = ℚ[t]` instance of P1, `ℚ[t] = MvPolynomial (Fin 1) ℚ` being the renamed t-line
`chartT` of `Mzk1G1B1SmoothCriterionSubmActual`.  With `g = h'(t)` this is the second factor of
the graph isomorphism `smoothModelRing h ≃ₐ[ℚ[λ]] ℚ[t][1/h']`. -/
theorem away_algEquiv_quotient_of_chartT (g : MvPolynomial (Fin 1) ℚ) :
    Nonempty ((Polynomial (MvPolynomial (Fin 1) ℚ) ⧸
        Ideal.span {Polynomial.C g * Polynomial.X - 1}) ≃ₐ[MvPolynomial (Fin 1) ℚ]
      Localization.Away g) :=
  away_algEquiv_quotient (MvPolynomial (Fin 1) ℚ) g

/-! ## Axiom checks -/

#print axioms away_algEquiv_quotient
#print axioms isLocalization_away_quotient
#print axioms isLocalization_away_quotient_of_chartT
#print axioms graphIso_lambda_side
#print axioms away_algEquiv_quotient_of_chartT

end LeanFormal.IUT.XiFPaper.Mzk1G1B1GraphIsoActual
