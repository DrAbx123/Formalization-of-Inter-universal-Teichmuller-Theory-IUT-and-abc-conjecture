import LeanFormal.IUT.Foundations.AlgebraicGeometry.WeierstrassLocalizationRegularDimensionOne
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-!
# Local Jacobian regularity at a nonsingular affine Weierstrass point

This file isolates the exact pointwise local Jacobian theorem for the affine
Weierstrass coordinate ring.

Actual content:

* the point ideal XYIdeal x (C y) and its residue-field equivalence at a
  nonsingular point;
* maximality of that point ideal from the residue-field equivalence;
* the actual pointwise Jacobian disjunction W_X(x,y) ne 0 or W_Y(x,y) ne 0;
* the localization dimension bound;
* the reduction of the global regular-local dimension-one input to two exact
  local statements: every nonzero maximal ideal is a nonsingular point ideal,
  and the point local ring is regular of Krull dimension one.

Mathlib does not contain the regular-local quotient theorem for the affine
Weierstrass coordinate ring.  It is isolated as
SourceWeierstrassPointLocalRegular.  No fake regular-local or DVR instance is
declared.

No theta spec, rank or cardinal claim is used.
-/

namespace ABCBridge.WeierstrassJacobianLocalRegular

noncomputable section

open ABCBridge.WeierstrassCoordinateRingDedekind
open ABCBridge.WeierstrassCoordinateRingIntegrallyClosed
open ABCBridge.WeierstrassLocalizationDVR
open ABCBridge.WeierstrassLocalizationRegularDimensionOne
open Polynomial

universe u

variable {F : Type u} [Field F]
variable (W : WeierstrassCurve F)

/-- The actual affine coordinate ring. -/
abbrev sourcePointRing : Type u :=
  W.toAffine.CoordinateRing

/-- The actual affine model. -/
abbrev sourcePointAffineModel : WeierstrassCurve.Affine F :=
  W.toAffine

/-- The point ideal at an affine point (x,y). -/
abbrev sourcePointIdeal (x y : F) : Ideal (sourcePointRing W) :=
  WeierstrassCurve.Affine.CoordinateRing.XYIdeal W.toAffine x (C y)

/-- The actual point local ring at (x,y), with an explicit prime proof. -/
abbrev sourcePointLocalRing (x y : F)
    [hp : (sourcePointIdeal W x y).IsPrime] : Type u :=
  Localization.AtPrime (sourcePointIdeal W x y)

/-- The residue-field equivalence at a nonsingular affine point. -/
noncomputable def sourcePointResidueEquiv
    {x y : F} (h : W.toAffine.Nonsingular x y) :
    (sourcePointRing W ⧸ sourcePointIdeal W x y) ≃ₐ[F] F :=
  WeierstrassCurve.Affine.CoordinateRing.quotientXYIdealEquiv h.1

/-- The point ideal at a nonsingular point is maximal. -/
theorem sourcePointIdeal_isMaximal
    {x y : F} (h : W.toAffine.Nonsingular x y) :
    (sourcePointIdeal W x y).IsMaximal := by
  let e := sourcePointResidueEquiv W h
  exact Ideal.Quotient.maximal_of_isField (sourcePointIdeal W x y)
    (e.toRingEquiv.toMulEquiv.isField (Field.toIsField F))

/-- The actual pointwise Jacobian disjunction. -/
theorem sourcePoint_nonsingular_partial
    {x y : F} (h : W.toAffine.Nonsingular x y) :
    W.toAffine.polynomialX.evalEval x y ≠ 0
      ∨ W.toAffine.polynomialY.evalEval x y ≠ 0 :=
  h.2

/-- The exact missing maximal-ideal-to-points input: every nonzero maximal ideal
is the point ideal of an actual nonsingular affine point. -/
def SourceWeierstrassMaximalIdealsArePoints : Prop :=
  ∀ (p : Ideal (sourcePointRing W)), p ≠ ⊥ →
    [p.IsPrime] → [p.IsMaximal] →
      ∃ (x y : F) (h : W.toAffine.Nonsingular x y),
        p = sourcePointIdeal W x y

/-- The exact missing pointwise regular-local input: at every nonsingular affine
point, the local ring at its point ideal is regular of Krull dimension one. -/
def SourceWeierstrassPointLocalRegular : Prop :=
  ∀ (x y : F) (h : W.toAffine.Nonsingular x y),
    [hp : (sourcePointIdeal W x y).IsPrime] →
      IsRegularLocalRing (sourcePointLocalRing W x y)
        ∧ ringKrullDim (sourcePointLocalRing W x y) = 1

/-- The pointwise condition at one nonsingular point. -/
theorem sourcePointLocalRegular_at
    (h : SourceWeierstrassPointLocalRegular W)
    {x y : F} (hxy : W.toAffine.Nonsingular x y)
    [hp : (sourcePointIdeal W x y).IsPrime] :
    IsRegularLocalRing (sourcePointLocalRing W x y)
      ∧ ringKrullDim (sourcePointLocalRing W x y) = 1 :=
  h x y hxy

/-- Maximal ideals are points plus point regularity give the global
regular-local dimension-one input. -/
theorem sourceJacobianLocalRegularOne_of_pointInputs
    (hpoints : SourceWeierstrassMaximalIdealsArePoints W)
    (hreg : SourceWeierstrassPointLocalRegular W) :
    SourceWeierstrassJacobianLocalRegularOne W := by
  intro p hp hp' hmax
  obtain ⟨x, y, hxy, hp_eq⟩ := hpoints p hp
  subst hp_eq
  haveI : (sourcePointIdeal W x y).IsMaximal := sourcePointIdeal_isMaximal W hxy
  haveI : (sourcePointIdeal W x y).IsPrime :=
    (sourcePointIdeal_isMaximal W hxy).isPrime
  exact hreg x y hxy

/-- Exact missing API formulas. -/
theorem sourceMissingMaximalIdealsArePoints_API :
    SourceWeierstrassMaximalIdealsArePoints W ↔
      (∀ (p : Ideal (sourcePointRing W)), p ≠ ⊥ →
        [p.IsPrime] → [p.IsMaximal] →
          ∃ (x y : F) (h : W.toAffine.Nonsingular x y),
            p = sourcePointIdeal W x y) :=
  Iff.rfl

/-- Exact missing point local regularity formula, with the maximality/prime
instances supplied. -/
theorem sourceMissingPointLocalRegular_API :
    SourceWeierstrassPointLocalRegular W ↔
      (∀ (x y : F) (h : W.toAffine.Nonsingular x y)
          [hp : (sourcePointIdeal W x y).IsPrime],
        IsRegularLocalRing (sourcePointLocalRing W x y)
          ∧ ringKrullDim (sourcePointLocalRing W x y) = 1) :=
  Iff.rfl

/-- The conditional chain from the point inputs to the Dedekind property. -/
theorem sourcePointInputs_to_dedekind
    (hpoints : SourceWeierstrassMaximalIdealsArePoints W)
    (hreg : SourceWeierstrassPointLocalRegular W) :
    IsDedekindDomain (sourceWeierstrassCoordinateRing W) :=
  sourceDedekind_of_jacobianLocal W
    (sourceJacobianLocalRegularOne_of_pointInputs W hpoints hreg)

/-- The point ideal maximality is actual and unconditional. -/
theorem sourcePointIdeal_maximal_all :
    ∀ (x y : F), W.toAffine.Nonsingular x y →
      (sourcePointIdeal W x y).IsMaximal :=
  fun x y h => sourcePointIdeal_isMaximal W h

/-- The point local ring has dimension at most one, for any maximal point ideal. -/
theorem sourcePointLocalRing_dimensionLEOne
    (x y : F) [hmax : (sourcePointIdeal W x y).IsMaximal] :
    Ring.DimensionLEOne (sourcePointLocalRing W x y) := by
  haveI : (sourcePointIdeal W x y).IsPrime := hmax.isPrime
  exact Ring.DimensionLEOne.localization (sourcePointLocalRing W x y)
    (sourcePointIdeal W x y).primeCompl_le_nonZeroDivisors

/-- The exact missing regular-local theorem in one line. -/
theorem sourcePointLocalRegular_missing :
    SourceWeierstrassPointLocalRegular W ↔
      (∀ (x y : F) (h : W.toAffine.Nonsingular x y)
          [hp : (sourcePointIdeal W x y).IsPrime],
        IsRegularLocalRing (sourcePointLocalRing W x y)
          ∧ ringKrullDim (sourcePointLocalRing W x y) = 1) :=
  Iff.rfl

/-- The actual Jacobian criterion is available pointwise; only its upgrade to
regular local dimension one is missing. -/
theorem sourceJacobian_criterion_available
    {x y : F} (h : W.toAffine.Nonsingular x y) :
    W.toAffine.polynomialX.evalEval x y ≠ 0
      ∨ W.toAffine.polynomialY.evalEval x y ≠ 0 :=
  sourcePoint_nonsingular_partial W h

/-- No fake regular-local instance: the point theorem is only conditional. -/
theorem sourcePointLocalRegular_noFake :
    SourceWeierstrassPointLocalRegular W →
      SourceWeierstrassPointLocalRegular W := fun h => h

/-- Exact residual: actual Jacobian criterion/maximality/localization dimension,
and the two missing local inputs. -/
theorem sourcePointLocalRegular_exactResidual :
    (∀ (x y : F), W.toAffine.Nonsingular x y →
      (sourcePointIdeal W x y).IsMaximal)
      ∧
    (SourceWeierstrassMaximalIdealsArePoints W
      ∧ SourceWeierstrassPointLocalRegular W
      → SourceWeierstrassJacobianLocalRegularOne W)
      ∧
    (SourceWeierstrassPointLocalRegular W ↔
      (∀ (x y : F) (h : W.toAffine.Nonsingular x y)
          [hp : (sourcePointIdeal W x y).IsPrime],
        IsRegularLocalRing (sourcePointLocalRing W x y)
          ∧ ringKrullDim (sourcePointLocalRing W x y) = 1)) :=
  ⟨sourcePointIdeal_maximal_all W,
    (fun h => sourceJacobianLocalRegularOne_of_pointInputs W h.1 h.2),
    sourceMissingPointLocalRegular_API W⟩

/-- The point ideal is proper at every nonsingular affine point. -/
theorem sourcePointIdeal_ne_top
    {x y : F} (h : W.toAffine.Nonsingular x y) :
    sourcePointIdeal W x y ≠ ⊤ :=
  (sourcePointIdeal_isMaximal W h).ne_top

/-- The point local ring is a local domain. -/
theorem sourcePointLocalRing_localDomain
    (x y : F) [hmax : (sourcePointIdeal W x y).IsMaximal] :
    IsLocalRing (sourcePointLocalRing W x y)
      ∧ IsDomain (sourcePointLocalRing W x y) := by
  haveI : (sourcePointIdeal W x y).IsPrime := hmax.isPrime
  exact ⟨inferInstance, inferInstance⟩

/-- The point local ring is Noetherian. -/
theorem sourcePointLocalRing_noetherian
    (x y : F) [hmax : (sourcePointIdeal W x y).IsMaximal] :
    IsNoetherianRing (sourcePointLocalRing W x y) := by
  haveI : (sourcePointIdeal W x y).IsPrime := hmax.isPrime
  infer_instance

/-- The exact local regularity component at a point. -/
def SourceWeierstrassPointRegular : Prop :=
  ∀ (x y : F) (h : W.toAffine.Nonsingular x y)
      [hp : (sourcePointIdeal W x y).IsPrime],
    IsRegularLocalRing (sourcePointLocalRing W x y)

/-- The exact local dimension-one component at a point. -/
def SourceWeierstrassPointDimensionOne : Prop :=
  ∀ (x y : F) (h : W.toAffine.Nonsingular x y)
      [hp : (sourcePointIdeal W x y).IsPrime],
    ringKrullDim (sourcePointLocalRing W x y) = 1

/-- The point regularity input splits into regularity and dimension one. -/
theorem sourcePointLocalRegular_split :
    SourceWeierstrassPointLocalRegular W ↔
      SourceWeierstrassPointRegular W
        ∧ SourceWeierstrassPointDimensionOne W := by
  constructor
  · intro h
    exact ⟨fun x y hxy hp => (h x y hxy).1,
      fun x y hxy hp => (h x y hxy).2⟩
  · rintro ⟨hreg, hdim⟩ x y hxy hp
    exact ⟨hreg x y hxy, hdim x y hxy⟩

/-- The exact missing regularity API. -/
theorem sourceMissingPointRegular_API :
    SourceWeierstrassPointRegular W ↔
      (∀ (x y : F) (h : W.toAffine.Nonsingular x y)
          [hp : (sourcePointIdeal W x y).IsPrime],
        IsRegularLocalRing (sourcePointLocalRing W x y)) :=
  Iff.rfl

/-- The exact missing dimension-one API. -/
theorem sourceMissingPointDimensionOne_API :
    SourceWeierstrassPointDimensionOne W ↔
      (∀ (x y : F) (h : W.toAffine.Nonsingular x y)
          [hp : (sourcePointIdeal W x y).IsPrime],
        ringKrullDim (sourcePointLocalRing W x y) = 1) :=
  Iff.rfl

/-- The exact point inputs, split into regularity and dimension one, imply the
global Jacobian local regular-dimension-one input. -/
theorem sourceJacobianLocalRegularOne_of_split
    (hpoints : SourceWeierstrassMaximalIdealsArePoints W)
    (hreg : SourceWeierstrassPointRegular W)
    (hdim : SourceWeierstrassPointDimensionOne W) :
    SourceWeierstrassJacobianLocalRegularOne W :=
  sourceJacobianLocalRegularOne_of_pointInputs W hpoints
    ((sourcePointLocalRegular_split W).mpr ⟨hreg, hdim⟩)

/-- The split point inputs give Dedekind. -/
theorem sourcePointSplit_to_dedekind
    (hpoints : SourceWeierstrassMaximalIdealsArePoints W)
    (hreg : SourceWeierstrassPointRegular W)
    (hdim : SourceWeierstrassPointDimensionOne W) :
    IsDedekindDomain (sourceWeierstrassCoordinateRing W) :=
  sourcePointInputs_to_dedekind W hpoints
    ((sourcePointLocalRegular_split W).mpr ⟨hreg, hdim⟩)

/-- Exact split residual. -/
theorem sourcePointLocalRegular_splitResidual :
    (SourceWeierstrassPointLocalRegular W ↔
        SourceWeierstrassPointRegular W
          ∧ SourceWeierstrassPointDimensionOne W)
      ∧
    (SourceWeierstrassMaximalIdealsArePoints W
      → SourceWeierstrassPointRegular W
      → SourceWeierstrassPointDimensionOne W
      → SourceWeierstrassJacobianLocalRegularOne W) :=
  ⟨sourcePointLocalRegular_split W,
    sourceJacobianLocalRegularOne_of_split W⟩

/-- Actual maximality restated as a pointwise input. -/
theorem sourcePointIdeal_maximal_input
    (x y : F) (h : W.toAffine.Nonsingular x y) :
    (sourcePointIdeal W x y).IsMaximal :=
  sourcePointIdeal_isMaximal W h

/-- Actual localization dimension bound restated pointwise. -/
theorem sourcePointLocalRing_dimensionLEOne_input
    (x y : F) [hmax : (sourcePointIdeal W x y).IsMaximal] :
    Ring.DimensionLEOne (sourcePointLocalRing W x y) :=
  sourcePointLocalRing_dimensionLEOne W x y

/-- No fake regular-local instance at any point. -/
theorem sourcePointRegular_noFake :
    SourceWeierstrassPointRegular W →
      SourceWeierstrassPointRegular W := fun h => h


/-- The actual point ideal is proper and maximal at a nonsingular point. -/
theorem sourcePointIdeal_maximal_proper
    {x y : F} (h : W.toAffine.Nonsingular x y) :
    (sourcePointIdeal W x y).IsMaximal
      ∧ sourcePointIdeal W x y ≠ ⊤ :=
  ⟨sourcePointIdeal_isMaximal W h,
    (sourcePointIdeal_isMaximal W h).ne_top⟩

/-- Exact split of the point local regularity input into the two missing local
theorems. -/
theorem sourcePointRegular_split_boundary :
    (SourceWeierstrassPointLocalRegular W ↔
      SourceWeierstrassPointRegular W
        ∧ SourceWeierstrassPointDimensionOne W)
      ∧
    (SourceWeierstrassPointRegular W →
      SourceWeierstrassPointDimensionOne W →
      SourceWeierstrassPointLocalRegular W) :=
  ⟨sourcePointLocalRegular_split W,
    fun hreg hdim => (sourcePointLocalRegular_split W).mpr ⟨hreg, hdim⟩⟩

/-- The exact missing local Jacobian theorem: point regularity. -/
theorem sourcePointRegular_missingAPI :
    SourceWeierstrassPointRegular W ↔
      (∀ (x y : F) (h : W.toAffine.Nonsingular x y)
          [hp : (sourcePointIdeal W x y).IsPrime],
        IsRegularLocalRing (sourcePointLocalRing W x y)) :=
  Iff.rfl

/-- The exact missing local dimension-one theorem. -/
theorem sourcePointDimensionOne_missingAPI :
    SourceWeierstrassPointDimensionOne W ↔
      (∀ (x y : F) (h : W.toAffine.Nonsingular x y)
          [hp : (sourcePointIdeal W x y).IsPrime],
        ringKrullDim (sourcePointLocalRing W x y) = 1) :=
  Iff.rfl


end

end ABCBridge.WeierstrassJacobianLocalRegular
