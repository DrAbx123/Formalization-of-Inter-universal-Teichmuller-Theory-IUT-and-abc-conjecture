import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionIsometry
import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionEmbeddingActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalIdealValuation
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

/-!
# Foundation F6b: normalized completion norm reducibility and the missing formula

This module continues Example36CompletionIsometry.  The remaining analytic input
for the normalized value compatibility is the normalized norm/valuation formula

  Real.log ||x|| = -(completionValuationExponent v x / e_w) * Real.log p,

equivalently ||x|| = p^(-nu/e_w), on the units of the tree's actual normalized
completion NormalizedCompletion place = Completion place =
(place.maximalIdeal).adicCompletion F, with e_w the relative ramification index.

## What is actually proved here

* the exact equivalence between the logarithmic form NormValuationCompatible
  and the p-power norm form ||x|| = p^(-nu/e) of the missing formula, for every
  positive e;
* the same equivalence with the spectral norm spelling of the normalized norm;
* the exact bridge between NormValuationCompatible and the value-group
  compatibility NormalizedValueCompatible of Example36CompletionEmbeddingActual
  (these are the same assertion, not two different hypotheses);
* the base-field norm comparison spectralNorm(algebraMap a) = ||a||_p;
* the conditional deductions at the actual ramification index e_w =
  relativeRamificationIndex (k := Q) place: the image log-norm identity
  (ImageLogNormCompatible), the normalized value compatibility
  (NormalizedValueCompatible), the actual (1/e_w)Z value lattice, and the
  kernel O_v^x of integral units, all under the single explicit hypothesis
  NormValuationCompatible place e_w.

## What remains missing (card)

The normalized norm/valuation formula itself is NOT proved here.  In the tree
the canonical completion norm satisfies the exact formula
log ||x|| = -nu(x) * log absNorm(place.maximalIdeal) (norm_eq_absNorm_zpow,
logNorm_eq_absNorm_mul); the missing step is the identification of the
normalized (spectral, Q_p-normalized) norm with the canonical norm raised to
the power 1/(e_w * f_w) (equivalently, the unit ball of the normalized spectral
norm with the integral unit ball of the canonical completion valuation).  That
analytic step is frozen in the card normalizedCompletionNormValuationFormulaCard
and is not assumed anywhere: every deduction below carries it as an explicit
hypothesis, so no fake norm formula and no unproved identification is used.

No theta, q-pilot, Tate or source-faithfulness claim is made.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open scoped NumberField
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {F : Type u} [Field F] [NumberField F]

/-! ## 1. The logarithmic, power and spectral spellings of the missing formula -/

theorem completionPadicPrime_one_lt (place : NumberField.FinitePlace F) :
    (1 : ℝ) < (completionPadicPrime place : ℝ) := by
  exact_mod_cast (Fact.out : Nat.Prime (completionPadicPrime place)).one_lt

/-- The missing normalized formula in p-power norm form is exactly equivalent
to its logarithmic form NormValuationCompatible. -/
theorem normValuationCompatible_iff_rpow (place : NumberField.FinitePlace F)
    (e : ℕ) (_he : 0 < e) :
    NormValuationCompatible (F := F) place e ↔
      ∀ x : (NormalizedPlaceCompletion place)ˣ,
        ‖((x : (NormalizedPlaceCompletion place)ˣ) :
            NormalizedPlaceCompletion place)‖ =
          (completionPadicPrime place : ℝ) ^
            (-((completionValuationExponent (place.maximalIdeal) x : ℝ) / (e : ℝ))) := by
  have hp : (0 : ℝ) < (completionPadicPrime place : ℝ) := by
    have h := completionPadicPrime_one_lt (F := F) place
    linarith
  constructor
  · intro h x
    have hx := h x
    have hnorm : 0 < ‖((x : (NormalizedPlaceCompletion place)ˣ) :
        NormalizedPlaceCompletion place)‖ := by
      exact norm_pos_iff.mpr (Units.ne_zero x)
    calc ‖((x : (NormalizedPlaceCompletion place)ˣ) :
            NormalizedPlaceCompletion place)‖
        = Real.exp (Real.log ‖((x : (NormalizedPlaceCompletion place)ˣ) :
            NormalizedPlaceCompletion place)‖) :=
          (Real.exp_log hnorm).symm
      _ = Real.exp (-((completionValuationExponent (place.maximalIdeal) x : ℝ) /
            (e : ℝ)) * Real.log (completionPadicPrime place : ℝ)) := by
          rw [hx]
      _ = Real.exp (Real.log (completionPadicPrime place : ℝ) *
            (-((completionValuationExponent (place.maximalIdeal) x : ℝ) /
              (e : ℝ)))) := by
          ring_nf
      _ = (completionPadicPrime place : ℝ) ^
            (-((completionValuationExponent (place.maximalIdeal) x : ℝ) /
              (e : ℝ))) :=
          (Real.rpow_def_of_pos hp _).symm
  · intro h x
    rw [h x, Real.log_rpow hp]

/-- The same missing formula rewritten with the spectral-norm spelling of the
normalized completion norm. -/
theorem normValuationCompatible_iff_spectralNorm (place : NumberField.FinitePlace F)
    (e : ℕ) (he : 0 < e) :
    NormValuationCompatible (F := F) place e ↔
      ∀ x : (NormalizedPlaceCompletion place)ˣ,
        spectralNorm (PadicScalarField place) (NormalizedPlaceCompletion place)
            (((x : (NormalizedPlaceCompletion place)ˣ) :
              NormalizedPlaceCompletion place)) =
          (completionPadicPrime place : ℝ) ^
            (-((completionValuationExponent (place.maximalIdeal) x : ℝ) / (e : ℝ))) := by
  rw [normValuationCompatible_iff_rpow (F := F) place e he]
  constructor
  · intro h x
    rw [← normalizedCompletion_norm_eq_spectralNorm
      (F := F) place (((x : (NormalizedPlaceCompletion place)ˣ) :
        NormalizedPlaceCompletion place))]
    exact h x
  · intro h x
    rw [normalizedCompletion_norm_eq_spectralNorm
      (F := F) place (((x : (NormalizedPlaceCompletion place)ˣ) :
        NormalizedPlaceCompletion place))]
    exact h x

/-! ## 2. The bridge to the value-group compatibility -/

/-- The logarithmic normalized norm/valuation formula NormValuationCompatible
and the value-group compatibility NormalizedValueCompatible of
Example36CompletionEmbeddingActual are the same assertion: both say that the
rational value of the image unit is the completion exponent divided by e. -/
theorem normalizedValueCompatible_iff_normValuation (place : NumberField.FinitePlace F)
    (e : ℕ)
    (φ : NormalizedPlaceCompletion place →ₐ[PadicScalarField place]
      PadicAlgCl (completionPadicPrime place)) :
    NormalizedValueCompatible (completionPadicPrime place) place.maximalIdeal e
        φ.toRingHom ↔
      NormValuationCompatible (F := F) place e := by
  rw [normalizedValueCompatible_iff_log_norm]
  exact imageLogNormCompatible_iff_normValuation (F := F) place e φ

/-- The actual normalized norm of a base-field scalar, written with the
spectral norm: it is the usual p-adic norm of the scalar.  This is the actual
base-field norm comparison available unconditionally. -/
theorem normalizedCompletion_spectralNorm_algebraMap
    (place : NumberField.FinitePlace F) (a : PadicScalarField place) :
    spectralNorm (PadicScalarField place) (NormalizedPlaceCompletion place)
        (algebraMap (PadicScalarField place) (NormalizedPlaceCompletion place) a) =
      ‖a‖ :=
  spectralNorm_extends a

/-! ## 3. Conditional deductions at the actual ramification index -/

/-- The image-side log-norm identity at e_w, under the missing normalized
norm/valuation formula. -/
theorem imageLogNormCompatible_ramification_of_normValuation
    (place : NumberField.FinitePlace F)
    (φ : NormalizedPlaceCompletion place →ₐ[PadicScalarField place]
      PadicAlgCl (completionPadicPrime place))
    (h : NormValuationCompatible (F := F) place
      (relativeRamificationIndex (k := ℚ) place)) :
    ImageLogNormCompatible (F := F) place
      (relativeRamificationIndex (k := ℚ) place) φ.toRingHom :=
  imageLogNormCompatible_ramification (F := F) place φ h

/-- The value-group compatibility at e_w, under the missing normalized
norm/valuation formula. -/
theorem normalizedValueCompatible_ramification_of_normValuation
    (place : NumberField.FinitePlace F)
    (φ : NormalizedPlaceCompletion place →ₐ[PadicScalarField place]
      PadicAlgCl (completionPadicPrime place))
    (h : NormValuationCompatible (F := F) place
      (relativeRamificationIndex (k := ℚ) place)) :
    NormalizedValueCompatible (completionPadicPrime place) place.maximalIdeal
      (relativeRamificationIndex (k := ℚ) place) φ.toRingHom :=
  (normalizedValueCompatible_iff_normValuation (F := F) place _ φ).mpr h

/-- The actual (1/e_w)Z value lattice of the image of the completion units,
under the missing normalized norm/valuation formula. -/
theorem completionImage_value_lattice_ramification_of_normValuation
    (place : NumberField.FinitePlace F)
    (φ : NormalizedPlaceCompletion place →ₐ[PadicScalarField place]
      PadicAlgCl (completionPadicPrime place))
    (h : NormValuationCompatible (F := F) place
      (relativeRamificationIndex (k := ℚ) place)) :
    Set.range (fun x : ((place.maximalIdeal).adicCompletion F)ˣ =>
        (padicAlgClUnitRationalLogVal (completionPadicPrime place)
          (unitsMapIntoPadicAlgCl (completionPadicPrime place) φ.toRingHom x)).toAdd) =
      Set.range (fun n : Int =>
        (n : ℚ) / (relativeRamificationIndex (k := ℚ) place : ℚ)) :=
  completionImage_value_lattice_actual (p := completionPadicPrime place)
    place.maximalIdeal (relativeRamificationIndex (k := ℚ) place)
    (Nat.pos_of_ne_zero (relativeRamificationIndex_ne_zero (k := ℚ) place))
    φ.toRingHom
    (normalizedValueCompatible_ramification_of_normValuation (F := F) place φ h)

/-- The kernel O_v^x of integral units of the image value map, under the missing
normalized norm/valuation formula. -/
theorem completionImage_value_eq_one_iff_integralUnits_ramification_of_normValuation
    (place : NumberField.FinitePlace F)
    (φ : NormalizedPlaceCompletion place →ₐ[PadicScalarField place]
      PadicAlgCl (completionPadicPrime place))
    (h : NormValuationCompatible (F := F) place
      (relativeRamificationIndex (k := ℚ) place))
    (x : ((place.maximalIdeal).adicCompletion F)ˣ) :
    padicAlgClUnitRationalLogVal (completionPadicPrime place)
        (unitsMapIntoPadicAlgCl (completionPadicPrime place) φ.toRingHom x) = 1 ↔
      x ∈ ((place.maximalIdeal).adicCompletionIntegers F).units :=
  completionImage_value_eq_one_iff_integralUnits_actual
    (p := completionPadicPrime place) place.maximalIdeal
    (relativeRamificationIndex (k := ℚ) place)
    (Nat.pos_of_ne_zero (relativeRamificationIndex_ne_zero (k := ℚ) place))
    φ.toRingHom
    (normalizedValueCompatible_ramification_of_normValuation (F := F) place φ h) x

/-! ## 4. The frozen missing-formula card -/

/-- The frozen target: the normalized norm/valuation formula at the actual
ramification index e_w.  This is a proposition; it is not proved in this file
and is not assumed anywhere. -/
def NormalizedCompletionNormValuationFormula (place : NumberField.FinitePlace F) :
    Prop :=
  NormValuationCompatible (F := F) place
    (relativeRamificationIndex (k := ℚ) place)

end Example36
end LeanFormal.IUT.IUTII.Frobenioid

namespace LeanFormal.IUT.Audit

/-- **Status card: the normalized completion norm/valuation formula.**

Actual part proved in Example36CompletionNormFormula: (i) the exact equivalence
between the logarithmic form NormValuationCompatible and the p-power norm form
||x|| = p^(-nu/e), for every positive e, and the same equivalence in
spectral-norm spelling; (ii) the exact bridge between NormValuationCompatible
and the value-group compatibility NormalizedValueCompatible; (iii) the
base-field comparison spectralNorm(algebraMap a) = ||a||_p; (iv) the conditional
deductions at e_w = relativeRamificationIndex (k := Q) place: the image
log-norm identity, the normalized value compatibility, the actual (1/e_w)Z
value lattice and the O_v^x kernel, all from the single explicit hypothesis
NormValuationCompatible place e_w.

Missing (NOT constructed, NOT claimed): the normalized norm/valuation formula
itself, i.e. NormValuationCompatible place e_w, equivalently ||x|| =
p^(-nu(x)/e_w) for the normalized (spectral, Q_p-normalized) completion norm.
The tree proves the canonical completion formula log ||x|| = -nu(x) *
log absNorm(place.maximalIdeal) (norm_eq_absNorm_zpow, logNorm_eq_absNorm_mul);
the missing step is the identification of the normalized spectral norm with
the canonical norm raised to the power 1/(e_w * f_w).  No fake norm formula and
no unproved identification is used; all deductions carry the formula as an
explicit hypothesis.  No theta, q-pilot, Tate or source-faithfulness claim. -/
def normalizedCompletionNormValuationFormulaCard : Obligation :=
  { id := "IUT-I-II.example36-normalized-completion-norm-formula"
    source := "IUT III, Example 3.6; normalized local log-norm row; " ++
      "completion value-group normalization"
    status := VerificationStatus.interface
    note := "Actual: equivalence of logarithmic and p-power norm forms; " ++
      "spectral-norm spelling; bridge to NormalizedValueCompatible; " ++
      "base-field spectral norm comparison; conditional deductions at e_w " ++
      "(image log-norm identity, normalized value compatibility, (1/e_w)Z " ++
      "value lattice, O_v^x kernel). Missing: the normalized norm/valuation " ++
      "formula NormValuationCompatible place e_w, i.e. the identification of " ++
      "the normalized spectral norm with canonical norm^(1/(e_w f_w)); the " ++
      "canonical completion norm formula itself is in the tree. No fake norm " ++
      "comparison; no theta/q/Tate claim."
    dependsOn :=
      [ "IUT-I-II.example36-completion-isometry",
        "IUT-I-II.example36-completion-embedding-actual" ] }

end LeanFormal.IUT.Audit
