import LeanFormal.IUT.Foundations.AlgebraicGeometry.UniformizerDVRDecomposition
import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedLogNormComparison
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import Mathlib.Topology.MetricSpace.ProperSpace

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Principal/torsion refinement of the DVR decomposition (L0.4 A/C batch)

`UniformizerDVRDecomposition.exists_uniformizer_dvr_decomposition` writes every
unit `u` of the canonical completion as `u = π^m * u0` with `u0` an actual
integral unit.  `NormalizedLogNormComparison` identifies the norm unit ball
`(Integers K)ˣ` with the valuation unit group `(Valued.v.integer)ˣ` and the
strict norm ball with the valuation principal units.

This file combines the two: under `ProperSpace K`, the production uniform
principal-unit exponent theorem produces a single positive `N` such that
`u0 ^ N` is principal for every integral unit `u0`.  Therefore the DVR
decomposition has an exact torsion boundary:

  `u = π^m * u0`,  and  `u0^N` is principal for one uniform `N > 0`.

The `ProperSpace K` input is supplied separately by
`ProperSpaceCanonicalCompletion.properSpace_canonicalCompletion`; this file keeps
it as an explicit hypothesis so the algebraic refinement can be audited
independently of the topological instance.  No fake properness instance is
declared here.

No card, no production edits.
-/

noncomputable section

namespace LeanFormal.IUT.DVRPrincipalRefinement

open scoped WithZero Valued
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.UniformizerDVRDecomposition
open LeanFormal.IUT.NormalizedLogNormComparison

universe u

local instance gaussianDVRRefinementIrreducibleFact :
    Fact (Irreducible
      (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨LeanFormal.IUT.gaussianPolynomial_irreducible⟩

/-- The canonical completion used throughout this file. -/
abbrev completionField : Type :=
  LeanFormal.IUT.UniformizerDVRDecomposition.completionField

/-- The actual valuation integer ring `Valued.v.integer`. -/
abbrev valuedInteger : Subring completionField :=
  LeanFormal.IUT.NormalizedLogNormComparison.valuedInteger

/-! ## Identification of the two integral unit groups -/

/-- The norm unit ball `Integers K` and the valuation integer ring
`Valued.v.integer` are the same subring; this is the ring equivalence induced by
the proved equality of subrings. -/
noncomputable def integersEquivValuedInteger :
    (LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField) ≃+*
      valuedInteger where
  toFun x := ⟨x.1, by
    rw [Valuation.mem_integer_iff]
    exact (norm_le_one_iff_valued_le_one x.1).mp
      ((LeanFormal.IUT.LocalFieldIntegralUnits.mem_integers_iff x.1).mp x.2)⟩
  invFun y := ⟨y.1, by
    rw [LeanFormal.IUT.LocalFieldIntegralUnits.mem_integers_iff]
    exact (norm_le_one_iff_valued_le_one y.1).mpr (by
      change (Valued.v y.1 : WithZero (Multiplicative ℤ)) ≤ 1
      exact y.2)⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_mul' x y := by ext; rfl
  map_add' x y := by ext; rfl

/-- The induced equivalence of actual integral unit groups. -/
noncomputable def integersUnitsEquivValuedInteger :
    (LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField)ˣ ≃*
      (valuedInteger)ˣ :=
  Units.mapEquiv (integersEquivValuedInteger).toMulEquiv

@[simp]
theorem integersUnitsEquivValuedInteger_apply_val
    (u : (LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField)ˣ) :
    (((integersUnitsEquivValuedInteger u).val).1 : completionField) =
      ((u.val).1 : completionField) :=
  rfl

@[simp]
theorem integersUnitsEquivValuedInteger_symm_apply_val
    (u : (valuedInteger)ˣ) :
    ((((integersUnitsEquivValuedInteger.symm u).val).1 : completionField)) =
      ((u.val).1 : completionField) :=
  rfl

/-! ## Uniform principal powers for actual valuation units -/

/-- Under properness, every actual valuation unit has a positive power which is
principal for the actual valuation.  This is the torsion boundary of the DVR
decomposition. -/
theorem exists_principalUnit_power_of_valuedInteger_unit
    [ProperSpace completionField] (u : (valuedInteger)ˣ) :
    ∃ N : ℕ, 0 < N ∧
      (Valued.v ((((u ^ N).val).1 : completionField) - 1) :
        WithZero (Multiplicative ℤ)) < 1 := by
  let e : (LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField)ˣ ≃*
      (valuedInteger)ˣ := integersUnitsEquivValuedInteger
  let v : (LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField)ˣ :=
    e.symm u
  obtain ⟨N, hNpos, hN⟩ :=
    LeanFormal.IUT.LocalFieldIntegralUnits.exists_uniform_principalUnit_exponent
      (K := completionField)
  refine ⟨N, hNpos, ?_⟩
  have hmem : v ^ N ∈ LeanFormal.IUT.LocalFieldIntegralUnits.principalUnits :=
    hN v
  rw [LeanFormal.IUT.LocalFieldIntegralUnits.mem_principalUnits_iff] at hmem
  have hmap : e (v ^ N) = u ^ N := by
    dsimp [v]
    rw [map_pow, MulEquiv.apply_symm_apply]
  have hval : ((((u ^ N).val).1 : completionField)) =
      ((((v ^ N).val).1 : completionField)) := by
    have h := congrArg
      (fun w : (valuedInteger)ˣ => (((w.val).1) : completionField)) hmap
    simpa [e, integersUnitsEquivValuedInteger, integersEquivValuedInteger,
      Units.mapEquiv] using h.symm
  rw [hval]
  exact (norm_lt_one_iff_valued_lt_one _).mp hmem

/-! ## Refined DVR decomposition -/

/-- **Principal/torsion refinement of the DVR decomposition.**  Every unit of the
canonical completion is `π^m` times an actual integral unit `u0`, and under
properness a single positive exponent `N` makes `u0^N` principal. -/
theorem exists_uniformizer_dvr_decomposition_with_principal_power
    [ProperSpace completionField] (u : completionFieldˣ) :
    ∃ m : ℤ, ∃ u0 : (valuedInteger)ˣ,
      (u : completionField) = concreteAdicUniformizer ^ m *
        ((u0.val).1 : completionField) ∧
      ∃ N : ℕ, 0 < N ∧
        (Valued.v ((((u0 ^ N).val).1 : completionField) - 1) :
          WithZero (Multiplicative ℤ)) < 1 := by
  obtain ⟨m, u0, hdec⟩ := exists_uniformizer_dvr_decomposition u
  obtain ⟨N, hNpos, hN⟩ := exists_principalUnit_power_of_valuedInteger_unit u0
  exact ⟨m, u0, hdec, N, hNpos, hN⟩

/-- Norm-spelling corollary of the refined decomposition: `u0^N` is within the
principal unit ball. -/
theorem exists_uniformizer_dvr_decomposition_with_norm_principal_power
    [ProperSpace completionField] (u : completionFieldˣ) :
    ∃ m : ℤ, ∃ u0 : (valuedInteger)ˣ,
      (u : completionField) = concreteAdicUniformizer ^ m *
        ((u0.val).1 : completionField) ∧
      ∃ N : ℕ, 0 < N ∧
        ‖((((u0 ^ N).val).1 : completionField)) - 1‖ < 1 := by
  obtain ⟨m, u0, hdec, N, hNpos, hNval⟩ :=
    exists_uniformizer_dvr_decomposition_with_principal_power u
  refine ⟨m, u0, hdec, N, hNpos, ?_⟩
  exact (norm_lt_one_iff_valued_lt_one _).mpr hNval

/-! ## Exact residual interface -/

/-- The refined decomposition is unconditional once properness of the canonical
completion is available.  The exact remaining topological object is
`ProperSpace canonicalCompletion`, supplied by
`ProperSpaceCanonicalCompletion.properSpace_canonicalCompletion` under the
missing `NormedSpace ℚ_[5]` structure.  This theorem records the consumer form
without adding a fake instance. -/
theorem exists_uniformizer_dvr_decomposition_with_principal_power_of_properSpace
    (hproper : ProperSpace completionField) (u : completionFieldˣ) :
    ∃ m : ℤ, ∃ u0 : (valuedInteger)ˣ,
      (u : completionField) = concreteAdicUniformizer ^ m *
        ((u0.val).1 : completionField) ∧
      ∃ N : ℕ, 0 < N ∧
        (Valued.v ((((u0 ^ N).val).1 : completionField) - 1) :
          WithZero (Multiplicative ℤ)) < 1 := by
  letI := hproper
  exact exists_uniformizer_dvr_decomposition_with_principal_power u


/-! ## Elementary properties of the two unit equivalences -/

@[simp]
theorem integersEquivValuedInteger_apply_val
    (x : LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField) :
    (((integersEquivValuedInteger x).1) : completionField) = (x.1 : completionField) :=
  rfl

@[simp]
theorem integersEquivValuedInteger_symm_apply_val
    (y : valuedInteger) :
    (((integersEquivValuedInteger.symm y).1) : completionField) =
      (y.1 : completionField) :=
  rfl

@[simp]
theorem integersUnitsEquivValuedInteger_apply
    (u : (LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField)ˣ) :
    integersUnitsEquivValuedInteger u =
      Units.mapEquiv (integersEquivValuedInteger).toMulEquiv u :=
  rfl

/-- The equivalence of integral unit groups preserves the underlying field
element. -/
theorem integersUnitsEquivValuedInteger_val
    (u : (LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField)ˣ) :
    (((integersUnitsEquivValuedInteger u).val).1 : completionField) =
      ((u.val).1 : completionField) :=
  rfl

/-- The inverse equivalence also preserves the underlying field element. -/
theorem integersUnitsEquivValuedInteger_symm_val
    (u : (valuedInteger)ˣ) :
    ((((integersUnitsEquivValuedInteger.symm u).val).1 : completionField)) =
      ((u.val).1 : completionField) :=
  rfl

/-! ## Principal units in the two unit balls -/

/-- Norm principal units are exactly the valuation principal units under the
canonical completion norm. -/
theorem mem_principalUnits_iff_valued_lt
    (u : (LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField)ˣ) :
    u ∈ LeanFormal.IUT.LocalFieldIntegralUnits.principalUnits ↔
      (Valued.v (((u.val).1 : completionField) - 1) :
        WithZero (Multiplicative ℤ)) < 1 :=
by
  rw [LeanFormal.IUT.LocalFieldIntegralUnits.mem_principalUnits_iff]
  exact norm_lt_one_iff_valued_lt_one _

/-- The principal-unit subgroup of the valuation integer units. -/
noncomputable def valuedPrincipalUnitsSubgroup : Subgroup (valuedInteger)ˣ :=
  (LeanFormal.IUT.LocalFieldIntegralUnits.principalUnits (K := completionField)).comap
    (integersUnitsEquivValuedInteger).symm.toMonoidHom

/-- The unit equivalence carries principal units to the valuation principal-unit
subgroup. -/
theorem integersUnitsEquivValuedInteger_mem_principalUnits_iff
    (u : (LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField)ˣ) :
    integersUnitsEquivValuedInteger u ∈ valuedPrincipalUnitsSubgroup ↔
      u ∈ LeanFormal.IUT.LocalFieldIntegralUnits.principalUnits :=
by
  rw [valuedPrincipalUnitsSubgroup, Subgroup.mem_comap]
  simp

/-! ## Consequences of the refined decomposition -/

/-- The refined decomposition restricted to integral units. -/
theorem exists_principal_power_for_integral_unit
    [ProperSpace completionField]
    (u : (valuedInteger)ˣ) :
    ∃ N : ℕ, 0 < N ∧
      (Valued.v ((((u ^ N).val).1 : completionField) - 1) :
        WithZero (Multiplicative ℤ)) < 1 :=
  exists_principalUnit_power_of_valuedInteger_unit u

/-- The uniform exponent can be chosen independent of `u`; this is the form
needed by torsion-boundary consumers. -/
theorem exists_uniform_torsion_boundary
    [ProperSpace completionField] :
    ∃ N : ℕ, 0 < N ∧
      ∀ u : (valuedInteger)ˣ,
        (Valued.v ((((u ^ N).val).1 : completionField) - 1) :
          WithZero (Multiplicative ℤ)) < 1 := by
  obtain ⟨N, hNpos, hN⟩ :=
    LeanFormal.IUT.LocalFieldIntegralUnits.exists_uniform_principalUnit_exponent
      (K := completionField)
  refine ⟨N, hNpos, ?_⟩
  intro u
  let e : (LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField)ˣ ≃*
      (valuedInteger)ˣ := integersUnitsEquivValuedInteger
  let v : (LeanFormal.IUT.LocalFieldIntegralUnits.Integers completionField)ˣ :=
    e.symm u
  have hmem : v ^ N ∈ LeanFormal.IUT.LocalFieldIntegralUnits.principalUnits :=
    hN v
  rw [LeanFormal.IUT.LocalFieldIntegralUnits.mem_principalUnits_iff] at hmem
  have hmap : e (v ^ N) = u ^ N := by
    dsimp [v]
    rw [map_pow, MulEquiv.apply_symm_apply]
  have hval : ((((u ^ N).val).1 : completionField)) =
      ((((v ^ N).val).1 : completionField)) := by
    have h := congrArg
      (fun w : (valuedInteger)ˣ => (((w.val).1) : completionField)) hmap
    simpa [e, integersUnitsEquivValuedInteger, integersEquivValuedInteger,
      Units.mapEquiv] using h.symm
  rw [hval]
  exact (norm_lt_one_iff_valued_lt_one _).mp hmem

end LeanFormal.IUT.DVRPrincipalRefinement

end