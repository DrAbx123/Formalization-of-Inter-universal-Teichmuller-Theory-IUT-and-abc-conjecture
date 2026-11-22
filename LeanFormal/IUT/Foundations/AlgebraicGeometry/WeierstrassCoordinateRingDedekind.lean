import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-!
# Dedekind structure of the affine Weierstrass coordinate ring

For a Weierstrass curve W over a field F, this file proves the actual components
of the Dedekind-domain criterion for the affine coordinate ring

  R = W.toAffine.CoordinateRing = F[X, Y] / (W(X,Y)):

* R is a domain (actual Mathlib instance);
* R is Noetherian (AdjoinRoot of a polynomial over the Noetherian ring F[X]);
* R has Krull dimension at most one, because it is module-finite (hence
  integral) over F[X], which is a principal ideal ring;
* R is a fraction ring of itself, so the remaining Dedekind condition is exactly
  integral closedness of R in FractionRing R.

The last condition is NOT available in the current Mathlib tree for affine
Weierstrass coordinate rings.  It is isolated as the exact missing input
SourceWeierstrassCoordinateRingIntegrallyClosed.  No fake Dedekind instance is
declared: the Dedekind theorem is conditional on that input.

No theta spec, rank or cardinal claim is used.
-/

namespace ABCBridge.WeierstrassCoordinateRingDedekind

noncomputable section

open Polynomial

universe u

variable {F : Type u} [Field F]
variable (W : WeierstrassCurve F)

/-- The actual affine coordinate ring F[W] of the Weierstrass curve. -/
abbrev sourceWeierstrassCoordinateRing : Type u :=
  W.toAffine.CoordinateRing

/-- The actual polynomial defining the affine coordinate ring. -/
abbrev sourceWeierstrassPolynomial : (Polynomial F)[X] :=
  W.toAffine.polynomial

/-- The actual monic polynomial relation. -/
theorem sourceWeierstrassPolynomial_monic :
    (sourceWeierstrassPolynomial W).Monic :=
  WeierstrassCurve.Affine.monic_polynomial (W := W.toAffine)

/-- The actual coordinate ring is the AdjoinRoot of the Weierstrass polynomial. -/
theorem sourceWeierstrassCoordinateRing_eq_adjoinRoot :
    sourceWeierstrassCoordinateRing W =
      AdjoinRoot (sourceWeierstrassPolynomial W) := rfl

/-- The actual coordinate ring is a domain. -/
theorem sourceWeierstrassCoordinateRing_isDomain :
    IsDomain (sourceWeierstrassCoordinateRing W) :=
  inferInstance

/-- The actual coordinate ring is module-finite over F[X]. -/
instance sourceWeierstrassCoordinateRing_moduleFinite :
    Module.Finite F[X] (sourceWeierstrassCoordinateRing W) :=
  (sourceWeierstrassPolynomial_monic W).finite_adjoinRoot

/-- The actual coordinate ring is Noetherian. -/
theorem sourceWeierstrassCoordinateRing_isNoetherian :
    IsNoetherianRing (sourceWeierstrassCoordinateRing W) :=
  inferInstance

/-- The actual coordinate ring has Krull dimension at most one, by integrality
over the principal ideal ring F[X]. -/
instance sourceWeierstrassCoordinateRing_dimensionLEOne :
    Ring.DimensionLEOne (sourceWeierstrassCoordinateRing W) :=
  Ring.DimensionLEOne.of_isIntegral (R := F[X])
    (B := sourceWeierstrassCoordinateRing W)

/-- The actual coordinate ring is integral over F[X]. -/
theorem sourceWeierstrassCoordinateRing_isIntegral :
    Algebra.IsIntegral F[X] (sourceWeierstrassCoordinateRing W) :=
  inferInstance

/-- The actual function field is the fraction field of the coordinate ring. -/
abbrev sourceWeierstrassFunctionField : Type u :=
  W.toAffine.FunctionField

/-- The function field is a fraction ring of the coordinate ring. -/
theorem sourceWeierstrassFunctionField_isFractionRing :
    IsFractionRing (sourceWeierstrassCoordinateRing W)
      (sourceWeierstrassFunctionField W) :=
  inferInstance

/-- The exact missing input: integral closedness of the affine Weierstrass
coordinate ring in its function field.  This is the smooth-affine-curve
condition not currently available in Mathlib for Weierstrass coordinate rings. -/
def SourceWeierstrassCoordinateRingIntegrallyClosed : Prop :=
  IsIntegrallyClosed (sourceWeierstrassCoordinateRing W)

/-- The two equivalent forms of the missing integral-closedness input. -/
theorem sourceWeierstrass_integrallyClosed_iff :
    SourceWeierstrassCoordinateRingIntegrallyClosed W ↔
      IsIntegrallyClosed (sourceWeierstrassCoordinateRing W) :=
  Iff.rfl

/-- The integral-closedness condition in fraction-field form. -/
theorem sourceWeierstrass_integrallyClosed_iff_fractionField :
    SourceWeierstrassCoordinateRingIntegrallyClosed W ↔
      ∀ {x : sourceWeierstrassFunctionField W},
        IsIntegral (sourceWeierstrassCoordinateRing W) x →
          ∃ y : sourceWeierstrassCoordinateRing W,
            algebraMap (sourceWeierstrassCoordinateRing W)
              (sourceWeierstrassFunctionField W) y = x :=
  (isIntegrallyClosed_iff (R := sourceWeierstrassCoordinateRing W)
    (sourceWeierstrassFunctionField W))

/-- Conditional Dedekind theorem from the exact missing integral-closedness
input, using the actual Mathlib criterion isDedekindDomain_iff. -/
theorem sourceWeierstrassCoordinateRing_isDedekindDomain_of_integrallyClosed
    (hint : SourceWeierstrassCoordinateRingIntegrallyClosed W) :
    IsDedekindDomain (sourceWeierstrassCoordinateRing W) := by
  rw [isDedekindDomain_iff (A := sourceWeierstrassCoordinateRing W)
    (sourceWeierstrassFunctionField W)]
  refine ⟨sourceWeierstrassCoordinateRing_isDomain W,
    sourceWeierstrassCoordinateRing_isNoetherian W,
    sourceWeierstrassCoordinateRing_dimensionLEOne W, ?_⟩
  intro x hx
  exact (isIntegrallyClosed_iff
    (sourceWeierstrassFunctionField W)).mp hint hx

/-- The conditional Dedekind theorem in the four-component form. -/
theorem sourceWeierstrassCoordinateRing_dedekind_iff_components :
    IsDedekindDomain (sourceWeierstrassCoordinateRing W) ↔
      IsDomain (sourceWeierstrassCoordinateRing W)
        ∧ IsNoetherianRing (sourceWeierstrassCoordinateRing W)
        ∧ Ring.DimensionLEOne (sourceWeierstrassCoordinateRing W)
        ∧ ∀ {x : sourceWeierstrassFunctionField W},
            IsIntegral (sourceWeierstrassCoordinateRing W) x →
              ∃ y : sourceWeierstrassCoordinateRing W,
                algebraMap (sourceWeierstrassCoordinateRing W)
                  (sourceWeierstrassFunctionField W) y = x :=
  isDedekindDomain_iff (A := sourceWeierstrassCoordinateRing W)
    (sourceWeierstrassFunctionField W)

/-- Forward direction: a Dedekind coordinate ring is integrally closed. -/
theorem sourceWeierstrass_integrallyClosed_of_isDedekindDomain
    (h : IsDedekindDomain (sourceWeierstrassCoordinateRing W)) :
    SourceWeierstrassCoordinateRingIntegrallyClosed W := by
  haveI := h
  exact (isIntegrallyClosed_iff_isIntegralClosure
    (sourceWeierstrassFunctionField W)).mpr inferInstance

/-- Exact equivalence: the source Dedekind property is equivalent to the
missing integral-closedness input, all other components being proved. -/
theorem sourceWeierstrass_dedekind_iff_integrallyClosed :
    IsDedekindDomain (sourceWeierstrassCoordinateRing W) ↔
      SourceWeierstrassCoordinateRingIntegrallyClosed W :=
  ⟨sourceWeierstrass_integrallyClosed_of_isDedekindDomain W,
    sourceWeierstrassCoordinateRing_isDedekindDomain_of_integrallyClosed W⟩

/-- Exact missing lemma/API: Mathlib does not currently provide the
integral-closedness instance for affine Weierstrass coordinate rings.  This is a
proposition, not an asserted instance. -/
theorem sourceWeierstrass_missing_integrallyClosed_API :
    SourceWeierstrassCoordinateRingIntegrallyClosed W ↔
      IsIntegrallyClosed (sourceWeierstrassCoordinateRing W) :=
  Iff.rfl

/-- No fake Dedekind instance: the Dedekind property is derived only from the
explicit integral-closedness input. -/
theorem sourceWeierstrass_noFakeDedekindInstance :
    SourceWeierstrassCoordinateRingIntegrallyClosed W →
      IsDedekindDomain (sourceWeierstrassCoordinateRing W) :=
  sourceWeierstrassCoordinateRing_isDedekindDomain_of_integrallyClosed W

/-- Actual proved components of the Dedekind criterion. -/
theorem sourceWeierstrass_proved_components :
    IsDomain (sourceWeierstrassCoordinateRing W)
      ∧ IsNoetherianRing (sourceWeierstrassCoordinateRing W)
      ∧ Ring.DimensionLEOne (sourceWeierstrassCoordinateRing W)
      ∧ Algebra.IsIntegral F[X] (sourceWeierstrassCoordinateRing W) :=
  ⟨sourceWeierstrassCoordinateRing_isDomain W,
    sourceWeierstrassCoordinateRing_isNoetherian W,
    sourceWeierstrassCoordinateRing_dimensionLEOne W,
    sourceWeierstrassCoordinateRing_isIntegral W⟩

/-- The exact boundary: all Dedekind components except integral closedness are
proved; integral closedness is isolated. -/
theorem sourceWeierstrass_dedekind_boundary :
    IsDedekindDomain (sourceWeierstrassCoordinateRing W) ↔
      SourceWeierstrassCoordinateRingIntegrallyClosed W :=
  sourceWeierstrass_dedekind_iff_integrallyClosed W

/-- The actual coordinate ring is a finitely generated F[X]-algebra. -/
theorem sourceWeierstrassCoordinateRing_isFiniteType :
    Algebra.FiniteType F[X] (sourceWeierstrassCoordinateRing W) :=
  inferInstance

/-- The actual coordinate ring is finitely presented over F[X]. -/
theorem sourceWeierstrassCoordinateRing_isFinitePresentation :
    Algebra.FinitePresentation F[X] (sourceWeierstrassCoordinateRing W) :=
  inferInstance

/-- The coordinate ring is a subring of its function field via the actual
algebra map. -/
theorem sourceWeierstrassCoordinateRing_algebraMap_injective :
    Function.Injective
      (algebraMap (sourceWeierstrassCoordinateRing W)
        (sourceWeierstrassFunctionField W)) :=
  IsFractionRing.injective (sourceWeierstrassCoordinateRing W)
    (sourceWeierstrassFunctionField W)

/-- The actual fraction-ring condition. -/
theorem sourceWeierstrassFunctionField_isFractionRing' :
    IsFractionRing (sourceWeierstrassCoordinateRing W)
      (sourceWeierstrassFunctionField W) :=
  inferInstance

/-- The missing integral-closedness condition is equivalent to the concrete
integral-closure statement in the fraction field. -/
theorem sourceWeierstrass_integrallyClosed_explicit :
    SourceWeierstrassCoordinateRingIntegrallyClosed W ↔
      IsIntegralClosure (sourceWeierstrassCoordinateRing W)
        (sourceWeierstrassCoordinateRing W)
        (sourceWeierstrassFunctionField W) :=
  isIntegrallyClosed_iff_isIntegralClosure
    (sourceWeierstrassFunctionField W)

/-- The Dedekind criterion with the three proved components substituted: the
only remaining condition is integral closedness. -/
theorem sourceWeierstrass_dedekind_criterion_reduced :
    IsDedekindDomain (sourceWeierstrassCoordinateRing W) ↔
      (∀ {x : sourceWeierstrassFunctionField W},
        IsIntegral (sourceWeierstrassCoordinateRing W) x →
          ∃ y : sourceWeierstrassCoordinateRing W,
            algebraMap (sourceWeierstrassCoordinateRing W)
              (sourceWeierstrassFunctionField W) y = x) := by
  rw [isDedekindDomain_iff (A := sourceWeierstrassCoordinateRing W)
    (sourceWeierstrassFunctionField W)]
  constructor
  · rintro ⟨_, _, _, hi⟩
    exact hi
  · intro hi
    exact ⟨sourceWeierstrassCoordinateRing_isDomain W,
      sourceWeierstrassCoordinateRing_isNoetherian W,
      sourceWeierstrassCoordinateRing_dimensionLEOne W, hi⟩

/-- The exact missing input in explicit integral-closure form. -/
theorem sourceWeierstrass_missing_integralClosure :
    SourceWeierstrassCoordinateRingIntegrallyClosed W ↔
      (∀ {x : sourceWeierstrassFunctionField W},
        IsIntegral (sourceWeierstrassCoordinateRing W) x →
          ∃ y : sourceWeierstrassCoordinateRing W,
            algebraMap (sourceWeierstrassCoordinateRing W)
              (sourceWeierstrassFunctionField W) y = x) :=
  sourceWeierstrass_integrallyClosed_iff_fractionField W

/-- The coordinate ring is a Noetherian domain (proved without Dedekind). -/
theorem sourceWeierstrassCoordinateRing_isNoetherianDomain :
    IsDomain (sourceWeierstrassCoordinateRing W)
      ∧ IsNoetherianRing (sourceWeierstrassCoordinateRing W) :=
  ⟨sourceWeierstrassCoordinateRing_isDomain W,
    sourceWeierstrassCoordinateRing_isNoetherian W⟩

/-- The coordinate ring has dimension at most one (proved). -/
theorem sourceWeierstrassCoordinateRing_dimension :
    Ring.DimensionLEOne (sourceWeierstrassCoordinateRing W) :=
  sourceWeierstrassCoordinateRing_dimensionLEOne W

/-- The coordinate ring is integral over F[X] (proved). -/
theorem sourceWeierstrassCoordinateRing_integral :
    Algebra.IsIntegral F[X] (sourceWeierstrassCoordinateRing W) :=
  sourceWeierstrassCoordinateRing_isIntegral W

/-- Exact boundary theorem: Dedekind iff the explicitly missing integral-closure
condition; the other three conditions are already proved. -/
theorem sourceWeierstrass_dedekind_boundary_explicit :
    IsDedekindDomain (sourceWeierstrassCoordinateRing W) ↔
      (∀ {x : sourceWeierstrassFunctionField W},
        IsIntegral (sourceWeierstrassCoordinateRing W) x →
          ∃ y : sourceWeierstrassCoordinateRing W,
            algebraMap (sourceWeierstrassCoordinateRing W)
              (sourceWeierstrassFunctionField W) y = x) :=
  sourceWeierstrass_dedekind_criterion_reduced W

/-- No global instance is declared; the conditional Dedekind theorem is the only
route, and it requires the exact missing input. -/
theorem sourceWeierstrass_dedekind_conditional_only :
    SourceWeierstrassCoordinateRingIntegrallyClosed W →
      IsDedekindDomain (sourceWeierstrassCoordinateRing W) :=
  sourceWeierstrassCoordinateRing_isDedekindDomain_of_integrallyClosed W


end

end ABCBridge.WeierstrassCoordinateRingDedekind
