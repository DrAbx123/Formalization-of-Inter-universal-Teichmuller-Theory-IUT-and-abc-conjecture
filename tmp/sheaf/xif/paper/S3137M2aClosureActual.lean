/-!
# S3137: M2a closure PARKED at one presentation-bridge step (task-67 relay)

Status: NOT closed.  All mathematics is done; one Lean presentation bridge
remains.  No declarations are provided by this module (doc-only, like qpilot's
parked S3133M2aClosedActual).  The proved tools live in
`S3137M2aToolActual` (EXIT0 + probe).

Goal (qpilot's exact Prop, unchanged):
  S3133RationalFiveCompletionNorm :
    ∃ hx : ((5:ℚ) : (comap (k:=ℚ) concreteGaussianFivePlace).maximalIdeal
              .adicCompletion ℚ) ≠ 0,
      ‖((5:ℚ) : ... )‖ = 5⁻¹.

Proved and reusable (S3137M2aToolActual, green):
* toAdd_unzero_eq_neg_one: WithZero-unzero additive exponent from valuation
  exp(-1) via WithZero.toAdd_unzero_eq_iff (fixes qpilot's motive blocker);
* norm_eq_absNorm_inv_of_valued_exp_neg_one: norm from valuation exp(-1) via
  NumberFieldFinitePlace.norm_eq_absNorm_zpow;
* rationalFivePlace_asIdeal_eq_span: contracted rational prime ideal = (5)
  (concreteGaussianFivePlace_comap + concreteFivePlace_maximalIdeal +
  concreteFiveHeightOne_asIdeal_eq_span);
* rationalFivePlace_valuation_five: base valuation of (5:ℚ) at the contracted
  place = exp(-1) via valuation_of_algebraMap + intValuation_singleton.

Remaining Lean-level exact missing (ONE bridge lemma):
  valued_coe_rat (v : HeightOneSpectrum (RingOfIntegers ℚ)) (x : ℚ) :
    Valued.v ((x:ℚ) : v.adicCompletion ℚ) = v.valuation ℚ x.
Mathlib has adicCompletion.valued_coe whose LHS is the WithVal presentation
  {toCompletion := ↑((WithVal.equiv (v.valuation ℚ)).symm x)}
while the goal element is the Coe/algebraMap presentation ↑x; and
adicCompletion.valuedAdicCompletion_def exposes
  Valued.v x = Valued.extensionValuation x.toCompletion
with the local instance `letI := v.adicValued`; the missing step is the
presentation equality between
  ((x:ℚ) : v.adicCompletion ℚ).toCompletion  and  ((x:ℚ) : (v.valuation ℚ).Completion)
under the Valued instance induced by v.adicValued, after which
  Valued.extensionValuation_apply_coe (K := ℚ) x
closes the bridge (attempted: rw [valuedAdicCompletion_def, coe_toCompletion]
did not match the presentation; Valued.extensionValuation_apply_coe works for
the generic Valued instance but the adicCompletion Valued instance is stated
through the *other* extensionValuation presentation).

Once valued_coe_rat is available, the M2a closure is two lines:
  hval := (valued_coe_rat rationalFivePlace.maximalIdeal 5).trans
            rationalFivePlace_valuation_five
  norm := norm_eq_absNorm_inv_of_valued_exp_neg_one ... hval,
        then concretePlace_lower_absNorm (absNorm = 5).
Then qpilot's S3133GaussianCanonicalQNorm_of_rationalCompletionNorm gives M2a;
their S3133R1StatusNoteActual/S3133GaussianModelMapResidualFinalActual design
fills R1 = M1 + M2b.

Recommendation to qpilot/mainline: prove valued_coe_rat in a Mathlib-adjacent
scratch file using Valued.extensionValuation_apply_coe for the v.adicValued
instance (the definitions are both in Mathlib/RingTheory/DedekindDomain/
AdicValuation.lean lines 590-760 and Mathlib/Topology/Algebra/Valued/
ValuedField.lean lines 285-360); no mathematics remains, only the presentation
coercion.  Do NOT import BaseScalarValuationRelation (broken upstream).
-/