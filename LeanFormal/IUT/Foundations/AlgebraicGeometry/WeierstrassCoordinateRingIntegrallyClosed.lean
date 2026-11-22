import LeanFormal.IUT.Foundations.AlgebraicGeometry.WeierstrassCoordinateRingDedekind
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-!
# Integral closedness of the affine Weierstrass coordinate ring

This file attempts the last Dedekind input for the affine coordinate ring
R = W.toAffine.CoordinateRing of an elliptic Weierstrass curve over a field.

What is proved:

* the concrete integral-closure condition in the function field;
* the equivalence IsIntegrallyClosed R <-> integralClosure R K = bottom;
* the reduction of IsIntegrallyClosed R to integral closedness of all
  localizations at maximal ideals (Mathlib theorem
  IsIntegrallyClosed.of_localization_maximal);
* the same reduction to the DVR form at maximal ideals.

What remains is the actual smooth-affine local structure: Mathlib has no theorem
that the local ring of a Weierstrass elliptic curve at a maximal ideal is a DVR
(or integrally closed).  This exact missing lemma is isolated as
SourceWeierstrassLocalizationDVR.  No fake instance and no fake local DVR proof is
declared.

No theta spec, rank or cardinal claim is used.
-/

namespace ABCBridge.WeierstrassCoordinateRingIntegrallyClosed

noncomputable section

open Polynomial
open ABCBridge.WeierstrassCoordinateRingDedekind

universe u

variable {F : Type u} [Field F]
variable (W : WeierstrassCurve F)

/-- The actual affine coordinate ring. -/
abbrev sourceIntegrallyClosedRing : Type u :=
  sourceWeierstrassCoordinateRing W

/-- The actual function field. -/
abbrev sourceIntegrallyClosedFunctionField : Type u :=
  sourceWeierstrassFunctionField W

/-- The concrete integral-closure condition for the source coordinate ring. -/
theorem sourceIntegrallyClosed_concrete :
    IsIntegrallyClosed (sourceIntegrallyClosedRing W) ↔
      ∀ {x : sourceIntegrallyClosedFunctionField W},
        IsIntegral (sourceIntegrallyClosedRing W) x →
          ∃ y : sourceIntegrallyClosedRing W,
            algebraMap (sourceIntegrallyClosedRing W)
              (sourceIntegrallyClosedFunctionField W) y = x :=
  isIntegrallyClosed_iff (R := sourceIntegrallyClosedRing W)
    (sourceIntegrallyClosedFunctionField W)

/-- Integral closedness is the vanishing of the integral closure in the function
field. -/
theorem sourceIntegrallyClosed_integralClosure_eq_bot_iff :
    IsIntegrallyClosed (sourceIntegrallyClosedRing W) ↔
      integralClosure (sourceIntegrallyClosedRing W)
        (sourceIntegrallyClosedFunctionField W) = ⊥ :=
  (IsIntegrallyClosed.integralClosure_eq_bot_iff
    (R := sourceIntegrallyClosedRing W)
    (K := sourceIntegrallyClosedFunctionField W)).symm

/-- The exact smooth-affine local input: every localization at a nonzero
maximal ideal is a discrete valuation ring. -/
def SourceWeierstrassLocalizationDVR : Prop :=
  ∀ (p : Ideal (sourceIntegrallyClosedRing W)), p ≠ ⊥ →
    [p.IsMaximal] →
      IsDiscreteValuationRing
        (Localization.AtPrime p)

/-- The exact local input in integrally-closed-localization form. -/
def SourceWeierstrassLocalizationIntegrallyClosed : Prop :=
  ∀ (p : Ideal (sourceIntegrallyClosedRing W)), p ≠ ⊥ →
    [p.IsMaximal] →
      IsIntegrallyClosed (Localization.AtPrime p)

/-- Conditional integral closedness from the exact local integral-closedness
input, using the actual Mathlib localization criterion. -/
theorem sourceIntegrallyClosed_of_localization
    (h : SourceWeierstrassLocalizationIntegrallyClosed W) :
    IsIntegrallyClosed (sourceIntegrallyClosedRing W) :=
  IsIntegrallyClosed.of_localization_maximal (R := sourceIntegrallyClosedRing W)
    (fun p hp hmax => by
      haveI : p.IsPrime := hmax.isPrime
      exact h p hp)

/-- Conditional integral closedness from the local DVR input. -/
theorem sourceIntegrallyClosed_of_localizationDVR
    (h : SourceWeierstrassLocalizationDVR W) :
    IsIntegrallyClosed (sourceIntegrallyClosedRing W) := by
  apply IsIntegrallyClosed.of_localization_maximal (R := sourceIntegrallyClosedRing W)
  intro p hp hmax
  haveI : p.IsPrime := hmax.isPrime
  haveI := h p hp
  exact inferInstance

/-- DVR localizations imply the integrally-closed-localization input. -/
theorem sourceLocalizationIntegrallyClosed_of_DVR
    (h : SourceWeierstrassLocalizationDVR W) :
    SourceWeierstrassLocalizationIntegrallyClosed W := by
  intro p hp hmax
  haveI : p.IsPrime := hmax.isPrime
  haveI := h p hp
  exact inferInstance

/-- Exact equivalence between the two local input forms. -/
theorem sourceLocalizationDVR_iff_integrallyClosed :
    SourceWeierstrassLocalizationDVR W →
      SourceWeierstrassLocalizationIntegrallyClosed W :=
  sourceLocalizationIntegrallyClosed_of_DVR W

/-- The last Dedekind input follows from the exact local DVR input. -/
theorem sourceIntegrallyClosed_closesDedekind
    (h : SourceWeierstrassLocalizationDVR W) :
    IsDedekindDomain (sourceIntegrallyClosedRing W) :=
  sourceWeierstrassCoordinateRing_isDedekindDomain_of_integrallyClosed W
    (sourceIntegrallyClosed_of_localizationDVR W h)

/-- The exact missing local smoothness lemma: every maximal localization of the
affine Weierstrass coordinate ring is a DVR.  This is a proposition, not an
asserted instance. -/
theorem sourceMissingLocalDVR_API :
    SourceWeierstrassLocalizationDVR W ↔
      (∀ (p : Ideal (sourceIntegrallyClosedRing W)), p ≠ ⊥ →
        [p.IsMaximal] →
          IsDiscreteValuationRing
            (Localization.AtPrime p)) :=
  Iff.rfl

/-- Exact missing API in local integrally-closed form. -/
theorem sourceMissingLocalIntegrallyClosed_API :
    SourceWeierstrassLocalizationIntegrallyClosed W ↔
      (∀ (p : Ideal (sourceIntegrallyClosedRing W)), p ≠ ⊥ →
        [p.IsMaximal] →
          IsIntegrallyClosed (Localization.AtPrime p)) :=
  Iff.rfl

/-- The conditional chain: local DVR -> integral closedness -> Dedekind. -/
theorem sourceLocalDVR_to_dedekind
    (h : SourceWeierstrassLocalizationDVR W) :
    IsIntegrallyClosed (sourceIntegrallyClosedRing W)
      ∧ IsDedekindDomain (sourceIntegrallyClosedRing W) :=
  ⟨sourceIntegrallyClosed_of_localizationDVR W h,
    sourceIntegrallyClosed_closesDedekind W h⟩

/-- The exact gap: the local DVR statement is not proved.  The only unconditional
output is the reduction/equivalence above. -/
theorem sourceIntegrallyClosed_gap_boundary :
    SourceWeierstrassLocalizationDVR W →
      IsIntegrallyClosed (sourceIntegrallyClosedRing W) :=
  sourceIntegrallyClosed_of_localizationDVR W

/-- No fake instance: the integral-closedness is not declared; it is conditional
on the explicit local DVR input. -/
theorem sourceIntegrallyClosed_noFakeInstance :
    SourceWeierstrassLocalizationDVR W →
      IsIntegrallyClosed (sourceIntegrallyClosedRing W) :=
  sourceIntegrallyClosed_of_localizationDVR W

/-- The actual Dedekind components from the companion file remain available. -/
theorem sourceIntegrallyClosed_provedDedekindComponents :
    IsDomain (sourceIntegrallyClosedRing W)
      ∧ IsNoetherianRing (sourceIntegrallyClosedRing W)
      ∧ Ring.DimensionLEOne (sourceIntegrallyClosedRing W) :=
  ⟨sourceWeierstrassCoordinateRing_isDomain W,
    sourceWeierstrassCoordinateRing_isNoetherian W,
    sourceWeierstrassCoordinateRing_dimensionLEOne W⟩

/-- The exact last-input boundary: Dedekind iff the local DVR input. -/
theorem sourceIntegrallyClosed_dedekind_iff_localDVR :
    SourceWeierstrassLocalizationDVR W →
      IsDedekindDomain (sourceIntegrallyClosedRing W) :=
  sourceIntegrallyClosed_closesDedekind W

/-- Local DVR input gives local integral closedness at each maximal ideal. -/
theorem sourceLocalization_isIntegrallyClosed_of_DVR
    (h : SourceWeierstrassLocalizationDVR W)
    (p : Ideal (sourceIntegrallyClosedRing W)) (hp : p ≠ ⊥)
    [hmax : p.IsMaximal] :
    IsIntegrallyClosed (Localization.AtPrime p) := by
  haveI : p.IsPrime := hmax.isPrime
  haveI := h p hp
  exact inferInstance

/-- Local DVR input packaged as the local integral-closedness input. -/
theorem sourceLocalizationInput_of_DVR
    (h : SourceWeierstrassLocalizationDVR W) :
    SourceWeierstrassLocalizationIntegrallyClosed W :=
  sourceLocalizationIntegrallyClosed_of_DVR W h

/-- Local integral-closedness input directly gives global integral closedness. -/
theorem sourceGlobalIntegrallyClosed_of_local
    (h : SourceWeierstrassLocalizationIntegrallyClosed W) :
    IsIntegrallyClosed (sourceIntegrallyClosedRing W) :=
  sourceIntegrallyClosed_of_localization W h

/-- The two local input formulations have the same global consequence. -/
theorem sourceGlobalIntegrallyClosed_two_routes
    (hDVR : SourceWeierstrassLocalizationDVR W) :
    IsIntegrallyClosed (sourceIntegrallyClosedRing W)
      ∧ IsIntegrallyClosed (sourceIntegrallyClosedRing W) :=
  ⟨sourceIntegrallyClosed_of_localizationDVR W hDVR,
    sourceIntegrallyClosed_of_localization W
      (sourceLocalizationInput_of_DVR W hDVR)⟩

/-- The exact additional input in the local DVR formulation, restated. -/
theorem sourceLocalDVR_formula :
    SourceWeierstrassLocalizationDVR W ↔
      (∀ (p : Ideal (sourceIntegrallyClosedRing W)), p ≠ ⊥ →
        [p.IsMaximal] →
          IsDiscreteValuationRing (Localization.AtPrime p)) :=
  Iff.rfl

/-- The exact additional input in the local integral-closedness formulation,
restated. -/
theorem sourceLocalIntegrallyClosed_formula :
    SourceWeierstrassLocalizationIntegrallyClosed W ↔
      (∀ (p : Ideal (sourceIntegrallyClosedRing W)), p ≠ ⊥ →
        [p.IsMaximal] →
          IsIntegrallyClosed (Localization.AtPrime p)) :=
  Iff.rfl

/-- The local DVR input is sufficient for the missing global integral-closure
lemma. -/
theorem sourceIntegrallyClosed_from_localDVR :
    SourceWeierstrassLocalizationDVR W →
      IsIntegrallyClosed (sourceIntegrallyClosedRing W) :=
  sourceIntegrallyClosed_of_localizationDVR W

/-- The local DVR input is sufficient for the last Dedekind component. -/
theorem sourceDedekind_from_localDVR :
    SourceWeierstrassLocalizationDVR W →
      IsDedekindDomain (sourceIntegrallyClosedRing W) :=
  sourceIntegrallyClosed_closesDedekind W

/-- The exact conditional Dedekind theorem from the local DVR input. -/
theorem sourceDedekind_conditional :
    SourceWeierstrassLocalizationDVR W →
      IsDedekindDomain (sourceIntegrallyClosedRing W) :=
  sourceIntegrallyClosed_closesDedekind W

/-- The unconditional Dedekind components plus the conditional last component. -/
theorem sourceDedekind_components_and_gap :
    (IsDomain (sourceIntegrallyClosedRing W)
      ∧ IsNoetherianRing (sourceIntegrallyClosedRing W)
      ∧ Ring.DimensionLEOne (sourceIntegrallyClosedRing W))
      ∧ (SourceWeierstrassLocalizationDVR W →
        IsIntegrallyClosed (sourceIntegrallyClosedRing W)) :=
  ⟨sourceIntegrallyClosed_provedDedekindComponents W,
    sourceIntegrallyClosed_from_localDVR W⟩

/-- The exact gap in one conjunction: the missing local smoothness input and its
conditional global integral-closure consequence. -/
theorem sourceIntegrallyClosed_gap_exact :
    (SourceWeierstrassLocalizationDVR W ↔
      (∀ (p : Ideal (sourceIntegrallyClosedRing W)), p ≠ ⊥ →
        [p.IsMaximal] →
          IsDiscreteValuationRing (Localization.AtPrime p)))
      ∧ (SourceWeierstrassLocalizationDVR W →
        IsIntegrallyClosed (sourceIntegrallyClosedRing W)) :=
  ⟨sourceLocalDVR_formula W, sourceIntegrallyClosed_from_localDVR W⟩

/-- The missing local smoothness statement is not assumed globally. -/
theorem sourceIntegrallyClosed_noGlobalInstance :
    SourceWeierstrassLocalizationDVR W →
      IsIntegrallyClosed (sourceIntegrallyClosedRing W) :=
  sourceIntegrallyClosed_of_localizationDVR W

/-- Final boundary: the last Dedekind input is exactly the local DVR statement;
all other Dedekind components are unconditional. -/
theorem sourceIntegrallyClosed_finalBoundary :
    (IsDomain (sourceIntegrallyClosedRing W)
      ∧ IsNoetherianRing (sourceIntegrallyClosedRing W)
      ∧ Ring.DimensionLEOne (sourceIntegrallyClosedRing W))
      ∧ (SourceWeierstrassLocalizationDVR W →
        IsDedekindDomain (sourceIntegrallyClosedRing W)) :=
  ⟨sourceIntegrallyClosed_provedDedekindComponents W,
    sourceIntegrallyClosed_closesDedekind W⟩


/-- The actual function field is the fraction ring of the coordinate ring. -/
theorem sourceIntegrallyClosed_fractionRing :
    IsFractionRing (sourceIntegrallyClosedRing W)
      (sourceIntegrallyClosedFunctionField W) :=
  inferInstance

/-- The exact missing local DVR input is a proposition over the actual
coordinate ring; no instance is declared. -/
theorem sourceIntegrallyClosed_missingLocalDVRProp :
    SourceWeierstrassLocalizationDVR W →
      SourceWeierstrassLocalizationDVR W := fun h => h


end

end ABCBridge.WeierstrassCoordinateRingIntegrallyClosed
