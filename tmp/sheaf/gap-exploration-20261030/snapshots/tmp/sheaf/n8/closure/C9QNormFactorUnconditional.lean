import tmp.sheaf.n8.closure.C9QNormFactorActual

/-!
# C9 q norm factor: attempted unconditional closure / exact gap

Task-220 attempts the unconditional E15 factor

  localSignedLog(qCandidate S) = d S * Real.log ||qUnit S||.

`C9QNormFactorActual.lean` already proves the exact equivalence with the
normalized spectral log formula and the conditional implication.  This file
records the strongest zero-sorry packaging and the exact repair obstruction.

Repair of the stale production chain was attempted:

- `LeanFormal/IUT/Foundations/AlgebraicGeometry/BaseScalarValuationRelation.lean`
  does not compile with the current tree.  Observed errors include:
  * line 39: `PadicScalarField place : Type` vs `Type u` universe mismatch;
  * line 46: deterministic `isDefEq` heartbeat timeout;
  * line 49: `Fact (Nat.Prime (pNat place))` instance mismatch;
  * line 59: `Rat.padicValuation_self` simplifier shape mismatch;
  * downstream errors in `valuation_completionMap`, `PadicInt.mkUnits`,
    `zpow_eq_one_iff_right₀` and `field_simp` API shapes.
- `GeneralNormalizedNormFormula.lean` and
  `GeneralNormalizedNormBySpectralUniqueness.lean` have no oleans and their
  sources also fail under the current API (`Valued` instance/`Real.log_zpow`
  errors).  Repairing them is a source-module change outside this file scope.

Therefore the unconditional factor is **not** proved here.  No axiom and no
sorry is introduced; the exact missing declaration is

```lean
NormalizedCanonicalQComparison S :
  normalizedQLog S =
    -((qCandidate S).exponent : Real) * log(absNorm (pF S)) / d S.
```

Equivalently, it is the normalized spectral norm formula at the q candidate.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT.N8Closure.C9QNormFactorUnconditional

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.C9QNormFactorActual

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PaperKf : Type := CommonPrimeCompletion (placeAtPrime S)

/-- Exact missing normalized spectral comparison (name re-exported for the
unconditional task). -/
def MissingNormalizedSpectralFormula : Prop :=
  NormalizedCanonicalQComparison S

theorem missingFormula_iff_qNormFactor :
    MissingNormalizedSpectralFormula S ↔ QNormFactor S :=
  (qNormFactor_iff_normalizedCanonicalQComparison S).symm

/-- Strongest zero-sorry conditional packaging: the E15 factor follows once the
missing normalized spectral formula is supplied. -/
theorem qNormFactor_of_missingNormalizedSpectralFormula
    (h : MissingNormalizedSpectralFormula S) : QNormFactor S :=
  qNormFactor_of_normalizedCanonicalQComparison S h

/-- The unconditional target, stated as the factor. -/
def UnconditionalQNormFactorTarget : Prop := QNormFactor S

theorem unconditionalTarget_iff_missingFormula :
    UnconditionalQNormFactorTarget S ↔ MissingNormalizedSpectralFormula S :=
  (missingFormula_iff_qNormFactor S).symm

end LeanFormal.IUT.N8Closure.C9QNormFactorUnconditional

end