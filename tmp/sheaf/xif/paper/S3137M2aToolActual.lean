import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceLogKummerIdentification
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter

/-!
# S3137: WithZero/norm/valuation tools for M2a (task-67; green part)

Reusable tools extracted from the task-67 M2a relay that are fully proved;
the remaining presentation bridge is documented in
`S3137M2aClosureActual` (parked).

* `toAdd_unzero_eq_neg_one`: valuation `exp(-1)` gives additive exponent `-1`
  without rewriting inside the `unzero` motive (uses
  `WithZero.toAdd_unzero_eq_iff`);
* `norm_eq_absNorm_inv_of_valued_exp_neg_one`: canonical completion norm of a
  nonzero element with valuation `exp(-1)` is the inverse absNorm base;
* `rationalFivePlace_asIdeal_eq_span` / `rationalFivePlace_valuation_five`: the
  rational place contracted from the Gaussian five place has prime ideal (5)
  and valuation of the rational scalar 5 equal to `exp(-1)` (via
  `valuation_of_algebraMap` + `intValuation_singleton`).
Consumers: qpilot M2a (once the presentation bridge lands), mainline R1,
lattice INDEX.R1.M2.base-q-transport.  Owner: lattice.  No sorry/axiom.
-/

noncomputable section
open scoped WithZero Valued BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3137M2aToolActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36

local instance s3137GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- **Unzero bridge**: a valuation equal to `exp(-1)` has additive exponent `-1`;
`WithZero.toAdd_unzero_eq_iff` avoids rewriting inside the `unzero` motive. -/
theorem toAdd_unzero_eq_neg_one
    {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0)
    (hval : x = WithZero.exp (-1 : ℤ)) :
    Multiplicative.toAdd (WithZero.unzero hx) = -1 := by
  rw [WithZero.toAdd_unzero_eq_iff hx]
  rw [hval]
  rfl

/-- **Norm bridge**: the canonical completion norm of a nonzero element with
valuation `exp(-1)` is the inverse absNorm base. -/
theorem norm_eq_absNorm_inv_of_valued_exp_neg_one
    {F : Type*} [Field F] [NumberField F]
    (P : NumberField.FinitePlace F) (x : P.maximalIdeal.adicCompletion F) (hx : x ≠ 0)
    (hval : Valued.v x = WithZero.exp (-1 : ℤ)) :
    ‖x‖ = (Ideal.absNorm P.maximalIdeal.asIdeal : ℝ)⁻¹ := by
  rw [NumberFieldFinitePlace.norm_eq_absNorm_zpow P x hx,
    toAdd_unzero_eq_neg_one (valuation_ne_zero_of_ne_zero P x hx) hval]
  rw [zpow_neg_one]

/-- The rational place contracted from the Gaussian five place. -/
abbrev rationalFivePlace : NumberField.FinitePlace ℚ :=
  NumberFieldFinitePlace.comap (k := ℚ) concreteGaussianFivePlace

/-- The rational prime ideal of the contracted place is the principal ideal (5). -/
theorem rationalFivePlace_asIdeal_eq_span :
    rationalFivePlace.maximalIdeal.asIdeal =
      Ideal.span {(5 : NumberField.RingOfIntegers ℚ)} := by
  rw [rationalFivePlace, concreteGaussianFivePlace_comap, concreteFivePlace_maximalIdeal]
  exact concreteFiveHeightOne_asIdeal_eq_span

/-- Valuation of the rational scalar 5 at the contracted place is `exp(-1)`. -/
theorem rationalFivePlace_valuation_five :
    (rationalFivePlace.maximalIdeal.valuation ℚ) (5 : ℚ) = WithZero.exp (-1 : ℤ) := by
  have halg : (algebraMap (NumberField.RingOfIntegers ℚ) ℚ
      (5 : NumberField.RingOfIntegers ℚ)) = (5 : ℚ) := by
    rw [show (5 : NumberField.RingOfIntegers ℚ) =
        ((5 : ℕ) : NumberField.RingOfIntegers ℚ) from rfl,
      map_natCast (algebraMap (NumberField.RingOfIntegers ℚ) ℚ) 5, Nat.cast_ofNat]
  rw [← halg]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := ℚ)
    (v := rationalFivePlace.maximalIdeal) (r := (5 : NumberField.RingOfIntegers ℚ))]
  exact IsDedekindDomain.HeightOneSpectrum.intValuation_singleton
    (v := rationalFivePlace.maximalIdeal) (r := (5 : NumberField.RingOfIntegers ℚ))
    (by exact_mod_cast (by norm_num : (5 : ℤ) ≠ 0)) rationalFivePlace_asIdeal_eq_span

end LeanFormal.IUT.XiFPaper.S3137M2aToolActual
