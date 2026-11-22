import LeanFormal.IUT.Foundations.AlgebraicGeometry.WeierstrassCoordinateRingIntegrallyClosed
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-!
# DVR localizations of the affine Weierstrass coordinate ring

This file reduces the exact missing local DVR statement

  for every nonzero maximal p, Localization.AtPrime p is a DVR

to two concrete local inputs from the actual regular-local API:

* the localization is a regular local ring;
* its Krull dimension is one.

Using Mathlib's actual theorem

  IsRegularLocalRing.iff_finrank_cotangentSpace

and the DVR criterion

  IsLocalRing.finrank_CotangentSpace_eq_one_iff,

these two inputs imply IsDiscreteValuationRing of the localization.  The
smoothness/Jacobian theorem that the affine Weierstrass local ring is regular of
dimension one is not available in the current Mathlib tree; it is isolated as
SourceWeierstrassLocalizationRegularDimensionOne.  No fake DVR instance is
declared.

No theta spec, rank or cardinal claim is used.
-/

namespace ABCBridge.WeierstrassLocalizationDVR

noncomputable section

open ABCBridge.WeierstrassCoordinateRingDedekind
open ABCBridge.WeierstrassCoordinateRingIntegrallyClosed

universe u

variable {F : Type u} [Field F]
variable (W : WeierstrassCurve F)

/-- The actual affine coordinate ring. -/
abbrev sourceLocalizationRing : Type u :=
  sourceWeierstrassCoordinateRing W

/-- The actual localization at a prime ideal. -/
abbrev sourceLocalizationAtPrime
    (p : Ideal (sourceLocalizationRing W)) [p.IsPrime] : Type u :=
  Localization.AtPrime p

/-- The exact local cotangent-space-one input: at every nonzero maximal ideal,
the cotangent space of the localization has residue-field dimension one. -/
def SourceWeierstrassLocalizationCotangentOne : Prop :=
  ∀ (p : Ideal (sourceLocalizationRing W)), p ≠ ⊥ →
    [p.IsPrime] → [p.IsMaximal] →
      Module.finrank
        (IsLocalRing.ResidueField (sourceLocalizationAtPrime W p))
        (IsLocalRing.CotangentSpace (sourceLocalizationAtPrime W p)) = 1

/-- The exact local regular-dimension-one input: at every nonzero maximal ideal,
the localization is regular local of Krull dimension one. -/
def SourceWeierstrassLocalizationRegularDimensionOne : Prop :=
  ∀ (p : Ideal (sourceLocalizationRing W)), p ≠ ⊥ →
    [p.IsPrime] → [p.IsMaximal] →
      IsRegularLocalRing (sourceLocalizationAtPrime W p)
        ∧ ringKrullDim (sourceLocalizationAtPrime W p) = 1

/-- A regular local ring of Krull dimension one is a DVR, via the actual
cotangent-space criterion. -/
theorem sourceLocalization_isDVR_of_regular_dimensionOne
    (p : Ideal (sourceLocalizationRing W)) (hp : p ≠ ⊥)
    [hp' : p.IsPrime] [hmax : p.IsMaximal]
    (hreg : IsRegularLocalRing (sourceLocalizationAtPrime W p))
    (hdim : ringKrullDim (sourceLocalizationAtPrime W p) = 1) :
    IsDiscreteValuationRing (sourceLocalizationAtPrime W p) := by
  apply (IsLocalRing.finrank_CotangentSpace_eq_one_iff
    (R := sourceLocalizationAtPrime W p)).mp
  have hreg' := (IsRegularLocalRing.iff_finrank_cotangentSpace
    (sourceLocalizationAtPrime W p)).mp hreg
  rw [hdim] at hreg'
  exact_mod_cast hreg'

/-- The regular-dimension-one input implies the exact DVR input at every
nonzero maximal ideal. -/
theorem sourceLocalizationDVR_of_regularDimensionOne
    (h : SourceWeierstrassLocalizationRegularDimensionOne W) :
    SourceWeierstrassLocalizationDVR W := by
  intro p hp hmax
  haveI : p.IsPrime := hmax.isPrime
  exact sourceLocalization_isDVR_of_regular_dimensionOne W p hp
    (h p hp).1 (h p hp).2

/-- The cotangent-one input implies the exact DVR input. -/
theorem sourceLocalizationDVR_of_cotangentOne
    (h : SourceWeierstrassLocalizationCotangentOne W) :
    SourceWeierstrassLocalizationDVR W := by
  intro p hp hmax
  haveI : p.IsPrime := hmax.isPrime
  exact (IsLocalRing.finrank_CotangentSpace_eq_one_iff
    (R := sourceLocalizationAtPrime W p)).mp (h p hp)

/-- Conversely, the exact DVR input gives cotangent dimension one. -/
theorem sourceLocalizationCotangentOne_of_DVR
    (h : SourceWeierstrassLocalizationDVR W) :
    SourceWeierstrassLocalizationCotangentOne W := by
  intro p hp hp' hmax
  haveI := h p hp
  exact IsLocalRing.finrank_CotangentSpace_eq_one
    (R := sourceLocalizationAtPrime W p)

/-- Exact equivalence between the DVR input and the cotangent-one input. -/
theorem sourceLocalizationDVR_iff_cotangentOne :
    SourceWeierstrassLocalizationDVR W ↔
      SourceWeierstrassLocalizationCotangentOne W :=
  ⟨sourceLocalizationCotangentOne_of_DVR W,
    sourceLocalizationDVR_of_cotangentOne W⟩

/-- The cotangent-one input gives the last integral-closure input. -/
theorem sourceIntegrallyClosed_of_cotangentOne
    (h : SourceWeierstrassLocalizationCotangentOne W) :
    IsIntegrallyClosed (sourceWeierstrassCoordinateRing W) :=
  sourceIntegrallyClosed_of_localizationDVR W
    (sourceLocalizationDVR_of_cotangentOne W h)

/-- The regular-dimension-one input gives the last integral-closure input. -/
theorem sourceIntegrallyClosed_of_regularDimensionOne
    (h : SourceWeierstrassLocalizationRegularDimensionOne W) :
    IsIntegrallyClosed (sourceWeierstrassCoordinateRing W) :=
  sourceIntegrallyClosed_of_localizationDVR W
    (sourceLocalizationDVR_of_regularDimensionOne W h)

/-- The regular-dimension-one input gives the Dedekind property. -/
theorem sourceDedekind_of_regularDimensionOne
    (h : SourceWeierstrassLocalizationRegularDimensionOne W) :
    IsDedekindDomain (sourceWeierstrassCoordinateRing W) :=
  sourceIntegrallyClosed_closesDedekind W
    (sourceLocalizationDVR_of_regularDimensionOne W h)

/-- The cotangent-one input gives the Dedekind property. -/
theorem sourceDedekind_of_cotangentOne
    (h : SourceWeierstrassLocalizationCotangentOne W) :
    IsDedekindDomain (sourceWeierstrassCoordinateRing W) :=
  sourceIntegrallyClosed_closesDedekind W
    (sourceLocalizationDVR_of_cotangentOne W h)

/-- The exact missing local smoothness input in regular-dimensional form. -/
theorem sourceMissingRegularDimensionOne_API :
    SourceWeierstrassLocalizationRegularDimensionOne W ↔
      (∀ (p : Ideal (sourceLocalizationRing W)), p ≠ ⊥ →
        [p.IsPrime] →
          [p.IsMaximal] →
          IsRegularLocalRing (sourceLocalizationAtPrime W p)
            ∧ ringKrullDim (sourceLocalizationAtPrime W p) = 1) :=
  Iff.rfl

/-- The exact missing local smoothness input in cotangent form. -/
theorem sourceMissingCotangentOne_API :
    SourceWeierstrassLocalizationCotangentOne W ↔
      (∀ (p : Ideal (sourceLocalizationRing W)), p ≠ ⊥ →
        [p.IsPrime] →
          [p.IsMaximal] →
          Module.finrank
            (IsLocalRing.ResidueField (sourceLocalizationAtPrime W p))
            (IsLocalRing.CotangentSpace (sourceLocalizationAtPrime W p)) = 1) :=
  Iff.rfl

/-- The exact two-step reduction: regular local dimension one -> cotangent
dimension one -> DVR. -/
theorem sourceRegularDimensionOne_to_DVR :
    SourceWeierstrassLocalizationRegularDimensionOne W →
      SourceWeierstrassLocalizationDVR W :=
  sourceLocalizationDVR_of_regularDimensionOne W

/-- Exact conditional residual: both missing local formulations are equivalent
to the DVR input, and give the last integral-closure/Dedekind inputs. -/
theorem sourceLocalizationDVR_exactResidual :
    (SourceWeierstrassLocalizationDVR W ↔
      SourceWeierstrassLocalizationCotangentOne W)
      ∧
    (SourceWeierstrassLocalizationRegularDimensionOne W →
      SourceWeierstrassLocalizationDVR W)
      ∧
    (SourceWeierstrassLocalizationCotangentOne W →
      IsIntegrallyClosed (sourceWeierstrassCoordinateRing W))
      ∧
    (SourceWeierstrassLocalizationRegularDimensionOne W →
      IsDedekindDomain (sourceWeierstrassCoordinateRing W)) :=
  ⟨sourceLocalizationDVR_iff_cotangentOne W,
    sourceLocalizationDVR_of_regularDimensionOne W,
    sourceIntegrallyClosed_of_cotangentOne W,
    sourceDedekind_of_regularDimensionOne W⟩

/-- No fake DVR instance: the DVR localization is only derived conditionally
from the explicit regular-dimension-one input. -/
theorem sourceLocalizationDVR_noFakeInstance :
    SourceWeierstrassLocalizationRegularDimensionOne W →
      SourceWeierstrassLocalizationDVR W :=
  sourceLocalizationDVR_of_regularDimensionOne W

/-- The actual local ring carries the Noetherian/local/domain structure needed by
the DVR criterion. -/
theorem sourceLocalization_localStructure
    (p : Ideal (sourceLocalizationRing W)) [hp : p.IsPrime] [hmax : p.IsMaximal] :
    IsLocalRing (sourceLocalizationAtPrime W p)
      ∧ IsNoetherianRing (sourceLocalizationAtPrime W p)
      ∧ IsDomain (sourceLocalizationAtPrime W p) := by
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The cotangent-one input with the local structure exposed. -/
theorem sourceLocalizationCotangentOne_localStructure
    (h : SourceWeierstrassLocalizationCotangentOne W)
    (p : Ideal (sourceLocalizationRing W)) (hp : p ≠ ⊥) [hp' : p.IsPrime] [hmax : p.IsMaximal] :
    Module.finrank
        (IsLocalRing.ResidueField (sourceLocalizationAtPrime W p))
        (IsLocalRing.CotangentSpace (sourceLocalizationAtPrime W p)) = 1
      ∧ IsLocalRing (sourceLocalizationAtPrime W p) :=
  ⟨h p hp, inferInstance⟩

/-- Conversely, the DVR input gives the regular-local dimension-one input. -/
theorem sourceRegularDimensionOne_of_DVR
    (h : SourceWeierstrassLocalizationDVR W) :
    SourceWeierstrassLocalizationRegularDimensionOne W := by
  intro p hp hp' hmax
  haveI := h p hp
  exact ⟨inferInstance, IsDiscreteValuationRing.ringKrullDim_eq_one
    (R := sourceLocalizationAtPrime W p)⟩

/-- Exact equivalence between the DVR input and the regular-local
dimension-one input. -/
theorem sourceLocalizationDVR_iff_regularDimensionOne :
    SourceWeierstrassLocalizationDVR W ↔
      SourceWeierstrassLocalizationRegularDimensionOne W :=
  ⟨sourceRegularDimensionOne_of_DVR W,
    sourceLocalizationDVR_of_regularDimensionOne W⟩

/-- Exact equivalence between the cotangent input and the regular-local
dimension-one input. -/
theorem sourceCotangentOne_iff_regularDimensionOne :
    SourceWeierstrassLocalizationCotangentOne W ↔
      SourceWeierstrassLocalizationRegularDimensionOne W := by
  rw [← sourceLocalizationDVR_iff_cotangentOne W,
    sourceLocalizationDVR_iff_regularDimensionOne W]

/-- The regular-local input at one maximal ideal gives the corresponding local
cotangent dimension. -/
theorem sourceRegularDimensionOne_cotangent
    (h : SourceWeierstrassLocalizationRegularDimensionOne W)
    (p : Ideal (sourceLocalizationRing W)) (hp : p ≠ ⊥)
    [hp' : p.IsPrime] [hmax : p.IsMaximal] :
    Module.finrank
        (IsLocalRing.ResidueField (sourceLocalizationAtPrime W p))
        (IsLocalRing.CotangentSpace (sourceLocalizationAtPrime W p)) = 1 := by
  have hreg := (h p hp).1
  have hdim := (h p hp).2
  have hcot := (IsRegularLocalRing.iff_finrank_cotangentSpace
    (sourceLocalizationAtPrime W p)).mp hreg
  rw [hdim] at hcot
  exact_mod_cast hcot

/-- The local DVR input at one maximal ideal gives regularity and dimension
one. -/
theorem sourceLocalizationDVR_localRegular
    (h : SourceWeierstrassLocalizationDVR W)
    (p : Ideal (sourceLocalizationRing W)) (hp : p ≠ ⊥)
    [hp' : p.IsPrime] [hmax : p.IsMaximal] :
    IsRegularLocalRing (sourceLocalizationAtPrime W p)
      ∧ ringKrullDim (sourceLocalizationAtPrime W p) = 1 := by
  haveI := h p hp
  exact ⟨inferInstance, IsDiscreteValuationRing.ringKrullDim_eq_one
    (R := sourceLocalizationAtPrime W p)⟩

/-- The exact missing input, exposed pointwise. -/
theorem sourceLocalizationDVR_pointwise
    (h : SourceWeierstrassLocalizationRegularDimensionOne W)
    (p : Ideal (sourceLocalizationRing W)) (hp : p ≠ ⊥)
    [hp' : p.IsPrime] [hmax : p.IsMaximal] :
    IsDiscreteValuationRing (sourceLocalizationAtPrime W p) :=
  sourceLocalization_isDVR_of_regular_dimensionOne W p hp
    (h p hp).1 (h p hp).2

/-- The conditional Dedekind theorem through the regular-local input. -/
theorem sourceLocalizationDVR_dedekind_conditional
    (h : SourceWeierstrassLocalizationRegularDimensionOne W) :
    IsDedekindDomain (sourceWeierstrassCoordinateRing W) :=
  sourceDedekind_of_regularDimensionOne W h

/-- The unconditional local structure plus conditional DVR input. -/
theorem sourceLocalizationDVR_components :
    (∀ (p : Ideal (sourceLocalizationRing W)), [p.IsPrime] → [p.IsMaximal] →
      IsLocalRing (sourceLocalizationAtPrime W p)
        ∧ IsNoetherianRing (sourceLocalizationAtPrime W p)
        ∧ IsDomain (sourceLocalizationAtPrime W p))
      ∧ (SourceWeierstrassLocalizationRegularDimensionOne W →
        SourceWeierstrassLocalizationDVR W) :=
  ⟨fun p hp hmax => sourceLocalization_localStructure W p,
    sourceLocalizationDVR_of_regularDimensionOne W⟩

/-- Exact residual with all three equivalent local formulations. -/
theorem sourceLocalizationDVR_allFormulations :
    (SourceWeierstrassLocalizationDVR W ↔
      SourceWeierstrassLocalizationCotangentOne W)
      ∧ (SourceWeierstrassLocalizationDVR W ↔
        SourceWeierstrassLocalizationRegularDimensionOne W)
      ∧ (SourceWeierstrassLocalizationRegularDimensionOne W →
        IsDedekindDomain (sourceWeierstrassCoordinateRing W)) :=
  ⟨sourceLocalizationDVR_iff_cotangentOne W,
    sourceLocalizationDVR_iff_regularDimensionOne W,
    sourceDedekind_of_regularDimensionOne W⟩


/-- The actual local ring at a nonzero maximal ideal is a local domain. -/
theorem sourceLocalization_localDomain
    (p : Ideal (sourceLocalizationRing W)) [hp : p.IsPrime] [hmax : p.IsMaximal] :
    IsLocalRing (sourceLocalizationAtPrime W p)
      ∧ IsDomain (sourceLocalizationAtPrime W p) :=
  ⟨inferInstance, inferInstance⟩

/-- The actual local ring at a nonzero maximal ideal is Noetherian. -/
theorem sourceLocalization_noetherian
    (p : Ideal (sourceLocalizationRing W)) [hp : p.IsPrime] [hmax : p.IsMaximal] :
    IsNoetherianRing (sourceLocalizationAtPrime W p) :=
  inferInstance

/-- The no-fake boundary: the only source of DVR is the explicit regular-local
dimension-one hypothesis. -/
theorem sourceLocalizationDVR_boundary :
    (SourceWeierstrassLocalizationRegularDimensionOne W →
      SourceWeierstrassLocalizationDVR W)
      ∧ (SourceWeierstrassLocalizationDVR W →
        IsDedekindDomain (sourceWeierstrassCoordinateRing W)) :=
  ⟨sourceLocalizationDVR_of_regularDimensionOne W,
    sourceIntegrallyClosed_closesDedekind W⟩


/-- The DVR input is exactly the missing local smoothness input; this records the
final boundary without a fake instance. -/
theorem sourceLocalizationDVR_missingSmoothnessBoundary :
    SourceWeierstrassLocalizationDVR W ↔
      SourceWeierstrassLocalizationRegularDimensionOne W :=
  sourceLocalizationDVR_iff_regularDimensionOne W


end

end ABCBridge.WeierstrassLocalizationDVR
