import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedLogNormComparison
import LeanFormal.IUT.Foundations.AlgebraicGeometry.CompletionProperSpaceConsumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.UniformizerDVRDecomposition
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import Mathlib.Tactic

/-!
# Source-normalization bridge: normalized ball, actual valuation, DVR units

This file links the normalized-norm comparison to the actual source
normalization and to the uniformizer DVR decomposition.  It records the exact
residuals that would be needed if the comparison were absent (the closed-ball
identity and the properness of the completed field), proves that neither
residual occurs for the actual concrete completion, and combines the DVR
decomposition with the transported principal-unit subgroup.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

noncomputable section

namespace LeanFormal.IUT.SourceNormalizationBridge

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.UniformizerDVRDecomposition
open scoped WithZero Valued

/-- Exact residual for the closed normalized unit ball: every element has
normalized norm at most one exactly when its actual valuation is integral. -/
def SourceNormalizationBallResidual : Prop :=
  forall x : completionField, ‖x‖ ≤ 1 ↔
    (Valued.v x : WithZero (Multiplicative Int)) ≤ 1

/-- Exact residual for the norm-one sphere. -/
def SourceNormalizationSphereResidual : Prop :=
  forall x : completionField, x ≠ 0 →
    (‖x‖ = 1 ↔ (Valued.v x : WithZero (Multiplicative Int)) = 1)

/-- Exact residual for properness of the actual completed field, needed by
the principal-unit exponent theorem. -/
def SourceProperSpaceResidual : Prop :=
  Nonempty (ProperSpace completionField)

/-- The closed-ball residual holds by the production normalized-norm
comparison. -/
theorem sourceNormalizationBallResidual_holds :
    SourceNormalizationBallResidual :=
  fun x => LeanFormal.IUT.NormalizedLogNormComparison.norm_le_one_iff_valued_le_one x

/-- The sphere residual holds by the production norm-one comparison. -/
theorem sourceNormalizationSphereResidual_holds :
    SourceNormalizationSphereResidual :=
  fun x hx => LeanFormal.IUT.NormalizedLogNormComparison.norm_one_iff_valued_one hx

/-- Properness of the concrete completed field is an actual instance. -/
theorem sourceProperSpaceResidual_holds : SourceProperSpaceResidual :=
  ⟨LeanFormal.IUT.CompletionProperSpaceConsumer.completionProperSpace⟩

/-- There is no missing closed-ball/sphere/properness premise for the source
normalization at the concrete DVR place. -/
theorem sourceNormalizationResidual_none :
    SourceNormalizationBallResidual ∧ SourceNormalizationSphereResidual ∧
      SourceProperSpaceResidual :=
  ⟨sourceNormalizationBallResidual_holds,
    sourceNormalizationSphereResidual_holds,
    sourceProperSpaceResidual_holds⟩

/-- A local properness instance for the completion, obtained from the actual
completed valuation structure. -/
noncomputable def sourceCompletionProperSpace : ProperSpace completionField :=
  LeanFormal.IUT.CompletionProperSpaceConsumer.completionProperSpace

/-- The normalized norm unit ball is the actual valuation integer ring. -/
theorem sourceNormBall_eq_valuedInteger :
    (LocalFieldIntegralUnits.Integers completionField : Subring completionField) =
      (Valued.v.integer : Subring completionField) :=
  LeanFormal.IUT.NormalizedLogNormComparison.norm_integer_eq_valued_integer

/-- The ring equivalence between the normalized norm unit ball and the
actual valuation integer ring. -/
noncomputable def sourceNormIntegerEquivValuedInteger :
    (LocalFieldIntegralUnits.Integers completionField) ≃+*
      (Valued.v.integer : Subring completionField) where
  toFun x := ⟨x.1, by
    rw [Valuation.mem_integer_iff]
    exact (LeanFormal.IUT.NormalizedLogNormComparison.norm_le_one_iff_valued_le_one x.1).mp
      ((mem_integers_iff x.1).mp x.2)⟩
  invFun y := ⟨y.1, by
    rw [mem_integers_iff]
    exact (LeanFormal.IUT.NormalizedLogNormComparison.norm_le_one_iff_valued_le_one y.1).mpr y.2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_mul' x y := by ext; rfl
  map_add' x y := by ext; rfl

@[simp] theorem sourceNormIntegerEquivValuedInteger_apply_coe
    (x : LocalFieldIntegralUnits.Integers completionField) :
    ((sourceNormIntegerEquivValuedInteger x :
        (Valued.v.integer : Subring completionField)) : completionField) =
      (x : completionField) := rfl

/-- The integral-unit equivalence induced by the norm/valuation subring
equality. -/
noncomputable def sourceNormUnitEquivValuedInteger :
    (LocalFieldIntegralUnits.Integers completionField)ˣ ≃*
      (Valued.v.integer : Subring completionField)ˣ :=
  Units.mapEquiv sourceNormIntegerEquivValuedInteger.toMulEquiv

@[simp] theorem sourceNormUnitEquivValuedInteger_apply_coe
    (u : (LocalFieldIntegralUnits.Integers completionField)ˣ) :
    ((((sourceNormUnitEquivValuedInteger u).val).1 : completionField)) =
      ((u : (LocalFieldIntegralUnits.Integers completionField)) : completionField) :=
  rfl

/-- The actual integral units under the normalized norm. -/
noncomputable def sourceNormPrincipalUnits :
    Subgroup (LocalFieldIntegralUnits.Integers completionField)ˣ :=
  principalUnits (K := completionField)

/-- The actual valuation principal units. -/
noncomputable def sourceValuedPrincipalUnits :
    Subgroup (Valued.v.integer : Subring completionField)ˣ :=
  (sourceNormPrincipalUnits).comap
    (sourceNormUnitEquivValuedInteger).symm.toMonoidHom

/-- Membership in the actual principal-unit subgroup is the strict valuation
condition. -/
theorem mem_sourceValuedPrincipalUnits_iff
    (u : (Valued.v.integer : Subring completionField)ˣ) :
    u ∈ sourceValuedPrincipalUnits ↔
      (Valued.v (((u.val).1 : completionField) - 1) :
        WithZero (Multiplicative Int)) < 1 := by
  unfold sourceValuedPrincipalUnits sourceNormPrincipalUnits
  rw [Subgroup.mem_comap, mem_principalUnits_iff]
  have hcoe : ((((sourceNormUnitEquivValuedInteger).symm u).val :
        LocalFieldIntegralUnits.Integers completionField) : completionField) =
      ((u.val).1 : completionField) := by
    dsimp [sourceNormUnitEquivValuedInteger, sourceNormIntegerEquivValuedInteger,
      Units.mapEquiv]
    rfl
  rw [hcoe]
  exact LeanFormal.IUT.NormalizedLogNormComparison.norm_lt_one_iff_valued_lt_one _

/-- The normalized principal units and the actual principal units are
multiplicatively equivalent through the integral-unit equivalence. -/
theorem sourceNormUnitEquiv_mem_valuedPrincipalUnits_iff
    (w : (LocalFieldIntegralUnits.Integers completionField)ˣ) :
    sourceNormUnitEquivValuedInteger w ∈ sourceValuedPrincipalUnits ↔
      w ∈ sourceNormPrincipalUnits :=
  by
  unfold sourceValuedPrincipalUnits
  rw [Subgroup.mem_comap]
  simp only [MulEquiv.symm_apply_apply]

/-- Every actual integral unit has a positive power in the actual principal
subgroup. -/
theorem exists_sourcePrincipalUnit_power
    (u : (Valued.v.integer : Subring completionField)ˣ) :
    ∃ N : Nat, 0 < N ∧ u ^ N ∈ sourceValuedPrincipalUnits := by
  let e : (LocalFieldIntegralUnits.Integers completionField)ˣ ≃*
      (Valued.v.integer : Subring completionField)ˣ :=
    sourceNormUnitEquivValuedInteger
  let w : (LocalFieldIntegralUnits.Integers completionField)ˣ := e.symm u
  letI : ProperSpace completionField :=
    LeanFormal.IUT.CompletionProperSpaceConsumer.completionProperSpace
  obtain ⟨N, hNpos, hN⟩ :=
    LocalFieldIntegralUnits.exists_uniform_principalUnit_exponent
      (K := completionField)
  refine ⟨N, hNpos, ?_⟩
  rw [sourceValuedPrincipalUnits, Subgroup.mem_comap]
  have hpow : e.symm (u ^ N) = w ^ N := by
    dsimp [w]
    rw [map_pow]
  rw [hpow]
  exact hN w

/-- Uniform principal exponent for all actual valuation integral units. -/
theorem exists_uniform_sourcePrincipalUnit_power :
    ∃ N : Nat, 0 < N ∧
      ∀ u : (Valued.v.integer : Subring completionField)ˣ,
        u ^ N ∈ sourceValuedPrincipalUnits := by
  letI : ProperSpace completionField :=
    LeanFormal.IUT.CompletionProperSpaceConsumer.completionProperSpace
  obtain ⟨N, hNpos, hN⟩ :=
    LocalFieldIntegralUnits.exists_uniform_principalUnit_exponent
      (K := completionField)
  refine ⟨N, hNpos, ?_⟩
  intro u
  unfold sourceValuedPrincipalUnits
  rw [Subgroup.mem_comap, map_pow]
  exact hN ((sourceNormUnitEquivValuedInteger).symm u)

/-- DVR decomposition with the integral part taken in the normalized norm unit
ball and with its uniform principal power. -/
theorem exists_uniformizer_dvr_normUnit_decomposition
    (u : completionFieldˣ) :
    ∃ m : Int, ∃ u0 : (LocalFieldIntegralUnits.Integers completionField)ˣ,
      (u : completionField) = concreteAdicUniformizer ^ m *
        ((u0 : (LocalFieldIntegralUnits.Integers completionField)) : completionField) ∧
      ∃ N : Nat, 0 < N ∧ u0 ^ N ∈ sourceNormPrincipalUnits := by
  obtain ⟨m, u0, hdec⟩ := exists_uniformizer_dvr_decomposition u
  let w : (LocalFieldIntegralUnits.Integers completionField)ˣ :=
    (sourceNormUnitEquivValuedInteger).symm u0
  have hcoe : ((w : (LocalFieldIntegralUnits.Integers completionField)) :
      completionField) = ((u0.val).1 : completionField) := rfl
  obtain ⟨N, hNpos, hprin⟩ := exists_sourcePrincipalUnit_power u0
  have hmap : sourceNormUnitEquivValuedInteger (w ^ N) = u0 ^ N := by
    dsimp [w]
    rw [map_pow, MulEquiv.apply_symm_apply]
  have hprincipal : w ^ N ∈ sourceNormPrincipalUnits :=
    (sourceNormUnitEquiv_mem_valuedPrincipalUnits_iff (w ^ N)).mp (by rwa [hmap])
  exact ⟨m, w, by rw [hcoe]; exact hdec, N, hNpos, hprincipal⟩

/-- Combined DVR decomposition and source principal refinement in valuation
form. -/
theorem exists_uniformizer_dvr_sourcePrincipalRefinement
    (u : completionFieldˣ) :
    ∃ m : Int, ∃ u0 : (Valued.v.integer : Subring completionField)ˣ,
      (u : completionField) = concreteAdicUniformizer ^ m *
        ((u0.val).1 : completionField) ∧
      ∃ N : Nat, 0 < N ∧ u0 ^ N ∈ sourceValuedPrincipalUnits := by
  obtain ⟨m, u0, hdec⟩ := exists_uniformizer_dvr_decomposition u
  obtain ⟨N, hNpos, hprin⟩ := exists_sourcePrincipalUnit_power u0
  exact ⟨m, u0, hdec, N, hNpos, hprin⟩

/-- Absolute-value-extension residual: the normalized norm and the actual
valuation determine the same closed unit ball.  This is the exact residual
that would be missing if only the strict-ball comparison were available. -/
def SourceAbsoluteValueExtensionResidual : Prop :=
  forall x : completionField, (‖x‖ ≤ 1 ↔
    (Valued.v x : WithZero (Multiplicative Int)) ≤ 1)

theorem sourceAbsoluteValueExtensionResidual_holds :
    SourceAbsoluteValueExtensionResidual :=
  sourceNormalizationBallResidual_holds

theorem sourceAbsoluteValueExtensionResidual_iff_ball :
    SourceAbsoluteValueExtensionResidual ↔ SourceNormalizationBallResidual :=
  Iff.rfl

/-- If properness were absent, that alone would be the residual in the DVR
principal refinement; here it is an actual instance. -/
theorem dvrPrincipalRefinementResidual_iff_properSpace :
    SourceProperSpaceResidual ↔ Nonempty (ProperSpace completionField) :=
  Iff.rfl

/-- The source principal-unit subgroup contains the identity. -/
theorem sourceValuedPrincipalUnits_one_mem :
    (1 : (Valued.v.integer : Subring completionField)ˣ) ∈
      sourceValuedPrincipalUnits :=
  (sourceValuedPrincipalUnits).one_mem

/-- The source principal-unit subgroup is closed under inverses. -/
theorem sourceValuedPrincipalUnits_inv_mem
    {u : (Valued.v.integer : Subring completionField)ˣ}
    (hu : u ∈ sourceValuedPrincipalUnits) :
    u⁻¹ ∈ sourceValuedPrincipalUnits :=
  (sourceValuedPrincipalUnits).inv_mem hu

/-- The source principal-unit subgroup is closed under multiplication. -/
theorem sourceValuedPrincipalUnits_mul_mem
    {u w : (Valued.v.integer : Subring completionField)ˣ}
    (hu : u ∈ sourceValuedPrincipalUnits)
    (hw : w ∈ sourceValuedPrincipalUnits) :
    u * w ∈ sourceValuedPrincipalUnits :=
  (sourceValuedPrincipalUnits).mul_mem hu hw

/-- The normalized principal units are the normalized principal subgroup
inside the norm unit ball. -/
theorem sourceNormPrincipalUnits_iff_norm_lt_one
    (u : (LocalFieldIntegralUnits.Integers completionField)ˣ) :
    u ∈ sourceNormPrincipalUnits ↔
      ‖((u : LocalFieldIntegralUnits.Integers completionField) : completionField) - 1‖ < 1 :=
  mem_principalUnits_iff u

/-- Units of the norm unit ball have norm one. -/
theorem sourceNorm_units_norm_one
    (u : (LocalFieldIntegralUnits.Integers completionField)ˣ) :
    ‖((u : LocalFieldIntegralUnits.Integers completionField) : completionField)‖ = 1 :=
  norm_unit_eq_one u

/-- The ring equivalence sends one to one. -/
@[simp] theorem sourceNormIntegerEquivValuedInteger_one :
    sourceNormIntegerEquivValuedInteger 1 = 1 :=
  map_one _

/-- The unit equivalence sends one to one. -/
@[simp] theorem sourceNormUnitEquivValuedInteger_one :
    sourceNormUnitEquivValuedInteger 1 = 1 :=
  map_one _

/-- The unit equivalence is multiplicative. -/
theorem sourceNormUnitEquivValuedInteger_mul
    (u w : (LocalFieldIntegralUnits.Integers completionField)ˣ) :
    sourceNormUnitEquivValuedInteger (u * w) =
      sourceNormUnitEquivValuedInteger u * sourceNormUnitEquivValuedInteger w :=
  map_mul _ _ _

/-- The unit equivalence is compatible with inverses. -/
theorem sourceNormUnitEquivValuedInteger_inv
    (u : (LocalFieldIntegralUnits.Integers completionField)ˣ) :
    sourceNormUnitEquivValuedInteger u⁻¹ =
      (sourceNormUnitEquivValuedInteger u)⁻¹ :=
  map_inv _ _ _

/-- Uniform exponent in the actual valuation form. -/
theorem exists_uniform_sourcePrincipalUnit_power_valued :
    ∃ N : Nat, 0 < N ∧
      ∀ u : (LocalFieldIntegralUnits.Integers completionField)ˣ,
        (Valued.v ((((sourceNormUnitEquivValuedInteger u).val).1 :
          completionField) - 1) : WithZero (Multiplicative Int)) < 1 := by
  obtain ⟨N, hNpos, hN⟩ := exists_uniform_sourcePrincipalUnit_power
  refine ⟨N, hNpos, ?_⟩
  intro u
  exact (mem_sourceValuedPrincipalUnits_iff _).mp
    (hN (sourceNormUnitEquivValuedInteger u))

/-- The source principal-unit subgroup contains one. -/
theorem sourceNormPrincipalUnits_one_mem : (1 : (LocalFieldIntegralUnits.Integers
    completionField)ˣ) ∈ sourceNormPrincipalUnits :=
  (sourceNormPrincipalUnits).one_mem

/-- The source norm principal-unit subgroup is closed under inverses. -/
theorem sourceNormPrincipalUnits_inv_mem
    {u : (LocalFieldIntegralUnits.Integers completionField)ˣ}
    (hu : u ∈ sourceNormPrincipalUnits) :
    u⁻¹ ∈ sourceNormPrincipalUnits :=
  (sourceNormPrincipalUnits).inv_mem hu

/-- The source norm principal-unit subgroup is closed under multiplication. -/
theorem sourceNormPrincipalUnits_mul_mem
    {u w : (LocalFieldIntegralUnits.Integers completionField)ˣ}
    (hu : u ∈ sourceNormPrincipalUnits)
    (hw : w ∈ sourceNormPrincipalUnits) :
    u * w ∈ sourceNormPrincipalUnits :=
  (sourceNormPrincipalUnits).mul_mem hu hw

/-- The source valuation principal-unit subgroup contains one. -/
theorem sourceValuedPrincipalUnits_one_mem_again :
    (1 : (Valued.v.integer : Subring completionField)ˣ) ∈
      sourceValuedPrincipalUnits :=
  (sourceValuedPrincipalUnits).one_mem

/-- The source valuation principal-unit subgroup is closed under powers. -/
theorem sourceValuedPrincipalUnits_pow_mem
    {u : (Valued.v.integer : Subring completionField)ˣ}
    (hu : u ∈ sourceValuedPrincipalUnits) (n : Nat) :
    u ^ n ∈ sourceValuedPrincipalUnits :=
  (sourceValuedPrincipalUnits).pow_mem hu n

/-- Coercion of the inverse ring equivalence. -/
@[simp] theorem sourceNormIntegerEquivValuedInteger_symm_apply_coe
    (y : (Valued.v.integer : Subring completionField)) :
    (((sourceNormIntegerEquivValuedInteger.symm y :
        LocalFieldIntegralUnits.Integers completionField)) : completionField) =
      (y : completionField) := rfl

/-- Coercion of the inverse unit equivalence. -/
@[simp] theorem sourceNormUnitEquivValuedInteger_symm_apply_coe
    (u : (Valued.v.integer : Subring completionField)ˣ) :
    ((((sourceNormUnitEquivValuedInteger.symm u).val :
        LocalFieldIntegralUnits.Integers completionField)) : completionField) =
      ((u.val).1 : completionField) := rfl

/-- The actual principal units are exactly the valuation-strict units. -/
theorem sourceValuedPrincipalUnits_iff_valued_lt_one
    (u : (Valued.v.integer : Subring completionField)ˣ) :
    u ∈ sourceValuedPrincipalUnits ↔
      (Valued.v (((u.val).1 : completionField) - 1) :
        WithZero (Multiplicative Int)) < 1 :=",
  mem_sourceValuedPrincipalUnits_iff u

/-- The source norm principal-unit subgroup is exactly the normalized-norm
principal subgroup. -/
theorem sourceNormPrincipalUnits_eq_principalUnits :
    sourceNormPrincipalUnits = principalUnits (K := completionField) :=",
  rfl

/-- The normalized-norm principal subgroup is contained in the full integral
unit group. -/
theorem sourceNormPrincipalUnits_le_integralUnits :
    (sourceNormPrincipalUnits :
      Subgroup (LocalFieldIntegralUnits.Integers completionField)ˣ) ≤ ⊤ :=",
  le_top

/-- The source valuation principal subgroup is contained in the full valuation
unit group. -/
theorem sourceValuedPrincipalUnits_le_units :
    (sourceValuedPrincipalUnits :
      Subgroup (Valued.v.integer : Subring completionField)ˣ) ≤ ⊤ :=",
  le_top

/-- The source valuation principal-unit subgroup is stable under inverse. -/
theorem sourceValuedPrincipalUnits_inv_iff
    (u : (Valued.v.integer : Subring completionField)ˣ) :
    u⁻¹ ∈ sourceValuedPrincipalUnits ↔ u ∈ sourceValuedPrincipalUnits := by
  constructor
  · intro h
    have h' : (u⁻¹)⁻¹ ∈ sourceValuedPrincipalUnits :=
      sourceValuedPrincipalUnits_inv_mem h
    simpa using h'
  · exact sourceValuedPrincipalUnits_inv_mem

end LeanFormal.IUT.SourceNormalizationBridge
