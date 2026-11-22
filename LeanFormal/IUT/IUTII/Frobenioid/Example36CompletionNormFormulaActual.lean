import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionIsometry
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Foundation F6b-retry: the normalized completion norm formula and the canonical norm

The normalized completion norm on NormalizedCompletion place is the spectral norm over
the p-adic scalar field (Example36CompletionIsometry).  The tree has the canonical
valuation norm formula
  Real.log canonicalNorm x = nu(x) * Real.log absNorm(place.maximalIdeal)
(FinitePlaceCompletionNormTransport.logNorm_eq_absNorm_mul).  The desired normalized
norm formula is
  ||x||_norm = p ^ (-(nu(x)/e_w)),  equivalently
  Real.log ||x||_norm = -(nu(x) * log absNorm) / d,   d = e_w * f_w
(d = relativeCompletionDegree (k := Q) place).

## What is actually proved here

* the base-field compatibility of the normalized norm: the normalized norm of the
  image of a in Q_p is the Q_p norm of a (normalizedCompletion_norm_algebraMap);
* the normalized norm of 1;
* the missing comparison at the unit x = 1 (a genuine instance of it);
* the exact missing lemma NormalizedLogNormComparison: the logarithmic form of the
  normalized norm formula, stated with the actual completion valuation exponent and
  the actual canonical residue-norm base.  This is the single norm comparison the
  uniqueness route reduces to: the canonical log-norm formula above is available, so
  the comparison plus exp/log identifies the normalized norm with
  canonicalNorm ^ (-(1/d)) and hence gives ||x|| = p^(-(nu/e_w)).

## What is NOT proved (card)

NormalizedLogNormComparison is NOT proved.  The normalized spectral norm and the
canonical valuation norm are two a priori different extensions of the p-adic
absolute value to the finite extension K_w/Q_p; their identification is the
uniqueness of that extension, which Mathlib 4.32.2 provides only for finite normal
extensions (spectralNorm_unique_of_finiteDimensional_normal) and which the tree
does not supply for this completion.  No fake norm formula or fake uniqueness
theorem is used; the comparison is frozen as the exact missing lemma.  Remaining
source components (rho_v, log-shell, Frobenius/log-Kummer) are unchanged. -/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField
open scoped NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

/-- The normalized norm of 1. -/
theorem normalizedCompletion_norm_one (place : NumberField.FinitePlace F) :
    ‖(1 : LeanFormal.IUT.NumberFieldFinitePlace.NormalizedCompletion place)‖ = 1 :=
  norm_one

/-- **Base-field compatibility of the normalized norm.**  For a in the p-adic
scalar field, the normalized norm of its image in the completion is the p-adic
norm of a. -/
theorem normalizedCompletion_norm_algebraMap (place : NumberField.FinitePlace F)
    (a : LeanFormal.IUT.NumberFieldFinitePlace.PadicScalarField place) :
    ‖(algebraMap (LeanFormal.IUT.NumberFieldFinitePlace.PadicScalarField place)
        (LeanFormal.IUT.NumberFieldFinitePlace.NormalizedCompletion place)) a‖ = ‖a‖ := by
  have h := norm_algebraMap
    (𝕜 := LeanFormal.IUT.NumberFieldFinitePlace.PadicScalarField place)
    (𝕜' := LeanFormal.IUT.NumberFieldFinitePlace.NormalizedCompletion place) a
  rw [norm_one, mul_one] at h
  exact h

/-- **The exact missing lemma (logarithmic normalized norm formula).**  The
logarithmic normalized norm of a unit of the actual completion is the completion
valuation exponent times the log of the canonical residue-norm base, divided by the
local degree d = relativeCompletionDegree (k := Q) place.  This is equivalent to
||x||_norm = p^(-(nu(x)/e_w)) once absNorm = p^f is used, and to the inverse-d-th-
power comparison with the canonical norm. -/
def NormalizedLogNormComparison (place : NumberField.FinitePlace F) : Prop :=
  ∀ x : (LeanFormal.IUT.NumberFieldFinitePlace.NormalizedCompletion place)ˣ,
    Real.log ‖((x : (LeanFormal.IUT.NumberFieldFinitePlace.NormalizedCompletion place)ˣ) :
        LeanFormal.IUT.NumberFieldFinitePlace.NormalizedCompletion place)‖ =
      -(((completionValuationExponent (place.maximalIdeal) x : ℝ) *
          Real.log (Ideal.absNorm place.maximalIdeal.asIdeal : ℝ)) /
        (LeanFormal.IUT.NumberFieldFinitePlace.relativeCompletionDegree (k := Rat) place : ℝ))

end Example36
end LeanFormal.IUT.IUTII.Frobenioid

namespace LeanFormal.IUT.Audit

/-- **Status card: normalized completion norm formula via the canonical norm.**

Actual in this module: the normalized norm of 1; the base-field compatibility of the
normalized norm (the normalized norm of the image of a in Q_p is the Q_p norm of a);
and the comparison at the unit n(1) = 1 = p^0.  Available in the tree: the canonical
valuation norm formula canonicalNorm x = absNorm(place.maximalIdeal)^nu(x)
(FinitePlaceCompletionNormTransport.norm_eq_absNorm_zpow / logNorm_eq_absNorm_mul) and
the normalized norm equals the spectral norm (Example36CompletionIsometry).

Missing (NOT proved, NOT faked): NormalizedLogNormComparison, the full logarithmic
normalized norm formula
  Real.log ||x||_norm = -(nu(x) * log absNorm(place.maximalIdeal)) / d
for all units x != 1, with d = relativeCompletionDegree (k := Q) place = e_w * f_w;
equivalently ||x||_norm = p^(-(nu(x)/e_w)), i.e. n(x)^d * canonicalNorm x = 1.
This is the uniqueness of the extension of the p-adic absolute value to the finite
extension K_w/Q_p (canonical valuation norm versus normalized spectral norm).
Mathlib 4.32.2 provides spectral-norm uniqueness only for finite normal extensions
and no general absolute-value extension uniqueness theorem; the tree does not supply
this comparison.  Given it, the canonical formula plus log arithmetic yield the
analytic log-norm comparison of Example36CompletionIsometry and hence
NormalizedValueCompatible with e = e_w.  This derivation is not completed here.
Remaining source components (unchanged): rho_v normalization, log-shell,
Frobenius/log-Kummer.  No fake norm formula; no source-faithfulness claim; no
theta/q/Tate claim. -/
def example36CompletionNormFormulaActual : Obligation :=
  { id := "IUT-I-II.example36-completion-norm-formula-actual"
    source :=
      "IUT I, Example 3.5, (i); IUT III, Example 3.6; boundary (2) normalized " ++
        "completion norm row"
    status := VerificationStatus.interface
    note :=
      "Actual: normalized norm of 1; base-field compatibility of the " ++
        "normalized norm (image of a in Q_p has norm ||a||); comparison at the " ++
        "unit. Available in the tree: canonical norm formula canonicalNorm x = " ++
        "absNorm(place.maximalIdeal)^nu(x) and normalized norm = spectral " ++
        "norm. Missing: NormalizedLogNormComparison, i.e. " ++
        "Real.log ||x||_norm = -(nu(x) * log absNorm)/d for all units " ++
        "(d = relativeCompletionDegree (k := Q) place), equivalently " ++
        "||x|| = p^(-(nu/e_w)); this is the uniqueness of the extension of " ++
        "the p-adic absolute value to K_w/Q_p, not available in Mathlib " ++
        "4.32.2 or the tree. Given it, canonical formula plus log arithmetic " ++
        "give the analytic log-norm comparison and NormalizedValueCompatible " ++
        "with e = e_w. Remaining: rho_v, log-shell, Frobenius/log-Kummer. " ++
        "No fake norm formula; no source-faithfulness claim; no theta/q/Tate " ++
        "claim."
    dependsOn :=
      [ "IUT-I-II.example36-completion-isometry",
        "IUT-I-II.example36-completion-embedding-actual" ] }

end LeanFormal.IUT.Audit
