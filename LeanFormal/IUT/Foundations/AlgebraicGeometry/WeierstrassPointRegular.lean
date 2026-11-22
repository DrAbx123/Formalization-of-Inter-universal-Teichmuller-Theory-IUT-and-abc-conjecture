import LeanFormal.IUT.Foundations.AlgebraicGeometry.WeierstrassJacobianLocalRegular
import Mathlib.RingTheory.KrullDimension.LocalRing
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-!
# Regularity and dimension one at a nonsingular affine Weierstrass point

This file proves the actual Krull-dimension-one half of the point local
Jacobian theorem and isolates the cotangent-space half.

Actual content:

* the point ideal XYIdeal x (C y) and its localization;
* the localized maximal ideal is nonzero, so the point local ring is not a
  field;
* the point local ring has Krull dimension at most one from
  Ring.DimensionLEOne.localization;
* consequently its Krull dimension is exactly one;
* the cotangent-space-one input implies IsRegularLocalRing via
  IsRegularLocalRing.iff_finrank_cotangentSpace;
* the exact missing Jacobian cotangent computation is isolated.

No fake regular-local or DVR instance is declared.
No theta spec, rank or cardinal claim is used.
-/

namespace ABCBridge.WeierstrassPointRegular

noncomputable section

open ABCBridge.WeierstrassCoordinateRingDedekind
open ABCBridge.WeierstrassCoordinateRingIntegrallyClosed
open ABCBridge.WeierstrassLocalizationDVR
open ABCBridge.WeierstrassLocalizationRegularDimensionOne
open ABCBridge.WeierstrassJacobianLocalRegular
open Polynomial

universe u

variable {F : Type u} [Field F]
variable (W : WeierstrassCurve F)

/-- The affine coordinate ring. -/
abbrev sourceRegularPointRing : Type u :=
  W.toAffine.CoordinateRing

/-- The point ideal XYIdeal x (C y). -/
abbrev sourceRegularPointIdeal (x y : F) : Ideal (sourceRegularPointRing W) :=
  WeierstrassCurve.Affine.CoordinateRing.XYIdeal W.toAffine x (C y)

/-- The point local ring. -/
abbrev sourceRegularPointLocalRing (x y : F)
    [hp : (sourceRegularPointIdeal W x y).IsPrime] : Type u :=
  Localization.AtPrime (sourceRegularPointIdeal W x y)


/-- The point ideal is nonzero: its X generator is a nonzero coordinate class. -/
theorem sourceRegularPointIdeal_ne_bot (x y : F) :
    sourceRegularPointIdeal W x y ≠ ⊥ := by
  intro hbot
  have hmem : WeierstrassCurve.Affine.CoordinateRing.XClass W.toAffine x
      ∈ sourceRegularPointIdeal W x y := by
    rw [sourceRegularPointIdeal]
    exact Ideal.subset_span (by simp)
  rw [hbot] at hmem
  exact (WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero (W' := W.toAffine) x)
    (by simpa using hmem)

/-- The localized maximal ideal is nonzero when the point ideal is nonzero. -/
theorem sourceRegularPoint_localization_maximalIdeal_ne_bot
    (x y : F) [hp : (sourceRegularPointIdeal W x y).IsPrime]
    (hne : sourceRegularPointIdeal W x y ≠ ⊥) :
    IsLocalRing.maximalIdeal (sourceRegularPointLocalRing W x y) ≠ ⊥ := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  intro hbot
  exact hne ((Ideal.map_eq_bot_iff_of_injective
    (IsLocalization.injective (sourceRegularPointLocalRing W x y)
      (sourceRegularPointIdeal W x y).primeCompl_le_nonZeroDivisors)).mp hbot)

/-- The point local ring is not a field when the point ideal is nonzero. -/
theorem sourceRegularPointLocalRing_not_field
    (x y : F) [hp : (sourceRegularPointIdeal W x y).IsPrime]
    (hne : sourceRegularPointIdeal W x y ≠ ⊥) :
    ¬ IsField (sourceRegularPointLocalRing W x y) := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]
  exact sourceRegularPoint_localization_maximalIdeal_ne_bot W x y hne

/-- The point local ring has Krull dimension at most one. -/
theorem sourceRegularPointLocalRing_dimensionLEOne
    (x y : F) [hp : (sourceRegularPointIdeal W x y).IsPrime] :
    Ring.DimensionLEOne (sourceRegularPointLocalRing W x y) :=
  Ring.DimensionLEOne.localization (sourceRegularPointLocalRing W x y)
    (sourceRegularPointIdeal W x y).primeCompl_le_nonZeroDivisors

/-- The point local ring has Krull dimension exactly one when the point ideal
is nonzero. -/
theorem sourceRegularPointLocalRing_ringKrullDim_eq_one
    (x y : F) [hp : (sourceRegularPointIdeal W x y).IsPrime]
    (hne : sourceRegularPointIdeal W x y ≠ ⊥) :
    ringKrullDim (sourceRegularPointLocalRing W x y) = 1 := by
  haveI : Ring.DimensionLEOne (sourceRegularPointLocalRing W x y) :=
    sourceRegularPointLocalRing_dimensionLEOne W x y
  have h1 : Ring.KrullDimLE 1 (sourceRegularPointLocalRing W x y) :=
    inferInstance
  have h0 : ¬ ringKrullDim (sourceRegularPointLocalRing W x y) ≤ 0 := by
    intro hle
    have hzero : Ring.KrullDimLE 0 (sourceRegularPointLocalRing W x y) :=
      Ring.krullDimLE_iff.mpr hle
    exact sourceRegularPointLocalRing_not_field W x y hne
      (Ring.KrullDimLE.isField_of_isDomain
        (R := sourceRegularPointLocalRing W x y))
  rw [Ring.krullDimLE_iff] at h1
  exact le_antisymm h1 (Order.succ_le_of_lt (lt_of_not_ge h0))

/-- The exact cotangent-space-one input at the point ideal. -/
def SourceWeierstrassPointCotangentOne
    (x y : F) [hp : (sourceRegularPointIdeal W x y).IsPrime] : Prop :=
  Module.finrank
    (IsLocalRing.ResidueField (sourceRegularPointLocalRing W x y))
    (IsLocalRing.CotangentSpace (sourceRegularPointLocalRing W x y)) = 1

/-- The cotangent-space-one input plus regularity criterion. -/
theorem sourceRegularPoint_isRegularLocal_of_cotangentOne
    (x y : F) [hp : (sourceRegularPointIdeal W x y).IsPrime]
    (hcot : SourceWeierstrassPointCotangentOne W x y)
    (hdim : ringKrullDim (sourceRegularPointLocalRing W x y) = 1) :
    IsRegularLocalRing (sourceRegularPointLocalRing W x y) :=
  (IsRegularLocalRing.iff_finrank_cotangentSpace
    (sourceRegularPointLocalRing W x y)).mpr (by
      rw [hcot, hdim]
      norm_num)

/-- The point regularity theorem from the cotangent-one input and dimension one. -/
theorem sourcePointRegular_of_cotangentOne_dimensionOne
    (x y : F) [hp : (sourceRegularPointIdeal W x y).IsPrime]
    (hcot : SourceWeierstrassPointCotangentOne W x y)
    (hdim : ringKrullDim (sourceRegularPointLocalRing W x y) = 1) :
    IsRegularLocalRing (sourceRegularPointLocalRing W x y)
      ∧ ringKrullDim (sourceRegularPointLocalRing W x y) = 1 :=
  ⟨sourceRegularPoint_isRegularLocal_of_cotangentOne W x y hcot hdim, hdim⟩

/-- The exact missing Jacobian cotangent computation: at a nonsingular point,
the localized point ideal has cotangent dimension one. -/
def SourceWeierstrassPointCotangentOneAll : Prop :=
  ∀ (x y : F) (h : W.toAffine.Nonsingular x y),
    letI : (sourceRegularPointIdeal W x y).IsPrime :=
      (sourcePointIdeal_isMaximal W h).isPrime
    SourceWeierstrassPointCotangentOne W x y

/-- The exact missing cotangent theorem, exposed. -/
theorem sourceMissingPointCotangentOne_API :
    SourceWeierstrassPointCotangentOneAll W ↔
      (∀ (x y : F) (h : W.toAffine.Nonsingular x y),
        letI : (sourceRegularPointIdeal W x y).IsPrime :=
          (sourcePointIdeal_isMaximal W h).isPrime
        Module.finrank
          (IsLocalRing.ResidueField (sourceRegularPointLocalRing W x y))
          (IsLocalRing.CotangentSpace (sourceRegularPointLocalRing W x y)) = 1) :=
  Iff.rfl

/-- The point regularity component follows from the missing cotangent input and
the proved dimension-one theorem. -/
theorem sourcePointRegular_of_cotangentAll
    (hcot : SourceWeierstrassPointCotangentOneAll W) :
    SourceWeierstrassPointRegular W := by
  intro x y h hprime
  haveI : (sourceRegularPointIdeal W x y).IsPrime :=
    (sourcePointIdeal_isMaximal W h).isPrime
  exact sourceRegularPoint_isRegularLocal_of_cotangentOne W x y (hcot x y h)
    (sourceRegularPointLocalRing_ringKrullDim_eq_one W x y
      (sourceRegularPointIdeal_ne_bot W x y))

/-- The point dimension-one component is proved unconditionally when the point
ideal is nonzero. -/
theorem sourcePointDimensionOne_actual :
    SourceWeierstrassPointDimensionOne W := by
  intro x y h hprime
  haveI : (sourceRegularPointIdeal W x y).IsPrime :=
    (sourcePointIdeal_isMaximal W h).isPrime
  exact sourceRegularPointLocalRing_ringKrullDim_eq_one W x y
    (sourceRegularPointIdeal_ne_bot W x y)

/-- Exact residual: actual dimension one, conditional regularity from cotangent
one, and the isolated missing cotangent computation. -/
theorem sourcePointRegular_exactResidual :
    SourceWeierstrassPointDimensionOne W
      ∧ (SourceWeierstrassPointCotangentOneAll W →
        SourceWeierstrassPointRegular W)
      ∧ (SourceWeierstrassPointCotangentOneAll W ↔
        (∀ (x y : F) (h : W.toAffine.Nonsingular x y),
          letI : (sourceRegularPointIdeal W x y).IsPrime :=
            (sourcePointIdeal_isMaximal W h).isPrime
          Module.finrank
            (IsLocalRing.ResidueField (sourceRegularPointLocalRing W x y))
            (IsLocalRing.CotangentSpace (sourceRegularPointLocalRing W x y)) = 1)) :=
  ⟨sourcePointDimensionOne_actual W,
    sourcePointRegular_of_cotangentAll W,
    sourceMissingPointCotangentOne_API W⟩

/-- No fake regular-local instance: only conditional on cotangent one. -/
theorem sourcePointRegular_noFake :
    SourceWeierstrassPointCotangentOneAll W →
      SourceWeierstrassPointRegular W :=
  sourcePointRegular_of_cotangentAll W

/-- The exact cotangent-one predicate at a point, restated. -/
theorem sourcePointCotangentOne_iff
    (x y : F) [hp : (sourceRegularPointIdeal W x y).IsPrime] :
    SourceWeierstrassPointCotangentOne W x y ↔
      Module.finrank
        (IsLocalRing.ResidueField (sourceRegularPointLocalRing W x y))
        (IsLocalRing.CotangentSpace (sourceRegularPointLocalRing W x y)) = 1 :=
  Iff.rfl

/-- The point local ring's maximal ideal is nonzero. -/
theorem sourcePointLocalRing_maximalIdeal_ne_bot
    (x y : F) [hp : (sourceRegularPointIdeal W x y).IsPrime] :
    IsLocalRing.maximalIdeal (sourceRegularPointLocalRing W x y) ≠ ⊥ :=
  sourceRegularPoint_localization_maximalIdeal_ne_bot W x y
    (sourceRegularPointIdeal_ne_bot W x y)

/-- The point local ring is not a field. -/
theorem sourcePointLocalRing_notField
    (x y : F) [hp : (sourceRegularPointIdeal W x y).IsPrime] :
    ¬ IsField (sourceRegularPointLocalRing W x y) :=
  sourceRegularPointLocalRing_not_field W x y
    (sourceRegularPointIdeal_ne_bot W x y)

/-- The actual dimension-one component at each point. -/
theorem sourcePointDimensionOne_actual' :
    ∀ (x y : F) (h : W.toAffine.Nonsingular x y)
        [hp : (sourceRegularPointIdeal W x y).IsPrime],
      ringKrullDim (sourceRegularPointLocalRing W x y) = 1 := by
  intro x y h hp
  exact sourceRegularPointLocalRing_ringKrullDim_eq_one W x y
    (sourceRegularPointIdeal_ne_bot W x y)

/-- The dimension-one component from the point regularity file is unconditional. -/
theorem sourcePointDimensionOne_unconditional :
    SourceWeierstrassPointDimensionOne W :=
  sourcePointDimensionOne_actual W

/-- Point regularity follows from the cotangent-one input and the actual
dimension-one theorem. -/
theorem sourcePointRegular_from_cotangentOne
    (x y : F) (h : W.toAffine.Nonsingular x y)
    [hp : (sourceRegularPointIdeal W x y).IsPrime]
    (hcot : SourceWeierstrassPointCotangentOne W x y) :
    IsRegularLocalRing (sourceRegularPointLocalRing W x y) :=
  sourceRegularPoint_isRegularLocal_of_cotangentOne W x y hcot
    (sourceRegularPointLocalRing_ringKrullDim_eq_one W x y
      (sourceRegularPointIdeal_ne_bot W x y))

/-- The exact point regularity input from the cotangent-one family. -/
theorem sourcePointRegularAll_of_cotangentAll
    (hcot : SourceWeierstrassPointCotangentOneAll W) :
    SourceWeierstrassPointRegular W :=
  sourcePointRegular_of_cotangentAll W hcot

/-- The point regularity and dimension-one components together give the point
local regular-dimension-one input of the preceding file. -/
theorem sourcePointLocalRegular_of_components
    (hreg : SourceWeierstrassPointRegular W) :
    SourceWeierstrassPointLocalRegular W :=
  (sourcePointLocalRegular_split W).mpr
    ⟨hreg, sourcePointDimensionOne_actual W⟩

/-- Conditional global chain: cotangent-one at all points -> point regularity ->
point local regular-dimension-one. -/
theorem sourcePointLocalRegular_of_cotangentAll
    (hcot : SourceWeierstrassPointCotangentOneAll W) :
    SourceWeierstrassPointLocalRegular W :=
  sourcePointLocalRegular_of_components W
    (sourcePointRegularAll_of_cotangentAll W hcot)

/-- The exact split: actual dimension one, conditional regularity. -/
theorem sourcePointRegular_splitExact :
    SourceWeierstrassPointDimensionOne W
      ∧ (SourceWeierstrassPointCotangentOneAll W →
        SourceWeierstrassPointRegular W) :=
  ⟨sourcePointDimensionOne_actual W,
    sourcePointRegularAll_of_cotangentAll W⟩

/-- The exact missing cotangent theorem is the only remaining pointwise input. -/
theorem sourcePointRegular_missingCotangent :
    SourceWeierstrassPointCotangentOneAll W →
      SourceWeierstrassPointRegular W :=
  sourcePointRegularAll_of_cotangentAll W

/-- No fake regular-local instance: regularity is conditional on cotangent one. -/
theorem sourcePointRegular_noFake' :
    SourceWeierstrassPointCotangentOneAll W →
      SourceWeierstrassPointRegular W :=
  sourcePointRegularAll_of_cotangentAll W


/-- The dimension-one component at a nonsingular point, without extra prime
hypotheses. -/
theorem sourcePointDimensionOne_nonsingular
    (x y : F) (h : W.toAffine.Nonsingular x y) :
    letI : (sourceRegularPointIdeal W x y).IsPrime :=
      (sourcePointIdeal_isMaximal W h).isPrime
    ringKrullDim (sourceRegularPointLocalRing W x y) = 1 := by
  letI : (sourceRegularPointIdeal W x y).IsPrime :=
    (sourcePointIdeal_isMaximal W h).isPrime
  exact sourceRegularPointLocalRing_ringKrullDim_eq_one W x y
    (sourceRegularPointIdeal_ne_bot W x y)

/-- The regularity component at a nonsingular point from cotangent one. -/
theorem sourcePointRegular_nonsingular
    (x y : F) (h : W.toAffine.Nonsingular x y)
    [hp : (sourceRegularPointIdeal W x y).IsPrime]
    (hcot : SourceWeierstrassPointCotangentOneAll W) :
    IsRegularLocalRing (sourceRegularPointLocalRing W x y) := by
  exact sourceRegularPoint_isRegularLocal_of_cotangentOne W x y
    (hcot x y h)
    (sourceRegularPointLocalRing_ringKrullDim_eq_one W x y
      (sourceRegularPointIdeal_ne_bot W x y))

/-- The cotangent-one family is exactly the missing pointwise cotangent
computation. -/
theorem sourcePointCotangentOneAll_iff :
    SourceWeierstrassPointCotangentOneAll W ↔
      (∀ (x y : F) (h : W.toAffine.Nonsingular x y),
        letI : (sourceRegularPointIdeal W x y).IsPrime :=
          (sourcePointIdeal_isMaximal W h).isPrime
        Module.finrank
          (IsLocalRing.ResidueField (sourceRegularPointLocalRing W x y))
          (IsLocalRing.CotangentSpace (sourceRegularPointLocalRing W x y)) = 1) :=
  Iff.rfl

/-- Exact split of the point local input into actual dimension-one and
conditional cotangent-regularity. -/
theorem sourcePointRegular_localInputBoundary :
    SourceWeierstrassPointDimensionOne W
      ∧ (SourceWeierstrassPointCotangentOneAll W →
        SourceWeierstrassPointRegular W) :=
  sourcePointRegular_splitExact W

/-- The conditional point local regular-dimension-one input. -/
theorem sourcePointLocalRegular_of_cotangentAll' :
    SourceWeierstrassPointCotangentOneAll W →
      SourceWeierstrassPointLocalRegular W :=
  sourcePointLocalRegular_of_cotangentAll W


end

end ABCBridge.WeierstrassPointRegular
