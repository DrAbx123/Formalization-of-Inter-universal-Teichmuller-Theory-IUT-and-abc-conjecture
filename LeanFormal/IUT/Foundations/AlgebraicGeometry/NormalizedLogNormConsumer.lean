import LeanFormal.IUT.Foundations.AlgebraicGeometry.NormalizedLogNormComparison
import LeanFormal.IUT.Foundations.AlgebraicGeometry.UniformizerDVRDecomposition
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits

/-!
# Consumer: normalized norm unit ball, DVR decomposition, principal refinement

This file consumes the production normalized-norm comparison and the actual
uniformizer DVR decomposition.  It constructs the integral-unit equivalence
between the normalized norm unit ball and Valued.v.integer, the corresponding
principal-unit subgroup, and the principal refinement.  The only input that is
not supplied by the production tree is properness of the concrete adic
completion; this is recorded exactly as CompletionProperSpaceResidual and all
principal-exponent results are stated relative to it.  No placeholder is used
and no new source data are introduced.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

noncomputable section

namespace LeanFormal.IUT.NormalizedLogNormConsumer

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.UniformizerDVRDecomposition
open scoped WithZero Valued

/-- The normalized norm unit ball and the actual valuation integer ring are the
same subring. -/
noncomputable def normIntegerEquivValuedInteger :
    (Integers completionField) ≃+* (Valued.v.integer : Subring completionField) where
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

@[simp] theorem normIntegerEquivValuedInteger_apply_coe
    (x : (Integers completionField)) :
    ((normIntegerEquivValuedInteger x :
        (Valued.v.integer : Subring completionField)) : completionField) =
      (x : completionField) := rfl

@[simp] theorem normIntegerEquivValuedInteger_symm_apply_coe
    (y : (Valued.v.integer : Subring completionField)) :
    (((normIntegerEquivValuedInteger.symm y : Integers completionField)) :
      completionField) = (y : completionField) := rfl

/-- The induced multiplicative equivalence of integral unit groups. -/
noncomputable def normUnitEquivValuedInteger :
    (Integers completionField)ˣ ≃*
      (Valued.v.integer : Subring completionField)ˣ :=
  Units.mapEquiv normIntegerEquivValuedInteger.toMulEquiv

@[simp] theorem normUnitEquivValuedInteger_apply_coe
    (u : (Integers completionField)ˣ) :
    ((((normUnitEquivValuedInteger u).val).1 : completionField)) =
      ((u : (Integers completionField)) : completionField) := rfl

/-- The actual principal-unit subgroup of the valuation integer ring. -/
noncomputable def valuedPrincipalUnits :
    Subgroup (Valued.v.integer : Subring completionField)ˣ :=
  (principalUnits (K := completionField)).comap
    (normUnitEquivValuedInteger).symm.toMonoidHom

/-- Membership in the actual principal-unit subgroup is the strict valuation
condition v(u-1) < 1. -/
theorem mem_valuedPrincipalUnits_iff
    (u : (Valued.v.integer : Subring completionField)ˣ) :
    u ∈ valuedPrincipalUnits ↔
      (Valued.v (((u.val).1 : completionField) - 1) :
        WithZero (Multiplicative Int)) < 1 := by
  rw [valuedPrincipalUnits, Subgroup.mem_comap, mem_principalUnits_iff]
  simpa only [normUnitEquivValuedInteger, normIntegerEquivValuedInteger,
    Units.mapEquiv] using
    (LeanFormal.IUT.NormalizedLogNormComparison.norm_lt_one_iff_valued_lt_one
      ((u.val).1 : completionField))

/-- The unit equivalence carries normalized principal units exactly onto the
actual principal-unit subgroup. -/
theorem normUnitEquiv_mem_valuedPrincipalUnits_iff
    (w : (Integers completionField)ˣ) :
    normUnitEquivValuedInteger w ∈ valuedPrincipalUnits ↔
      w ∈ principalUnits (K := completionField) := by
  dsimp only [valuedPrincipalUnits, Subgroup.mem_comap]
  rw [(normUnitEquivValuedInteger).symm_apply_apply w]

/-- The principal-unit subgroups on the two integer rings are multiplicatively
equivalent. -/
noncomputable def principalUnitsEquivValued :
    principalUnits (K := completionField) ≃* valuedPrincipalUnits where
  toFun w := ⟨normUnitEquivValuedInteger (w : (Integers completionField)ˣ),
    (normUnitEquiv_mem_valuedPrincipalUnits_iff
      (w : (Integers completionField)ˣ)).mpr w.property⟩
  invFun v := ⟨(normUnitEquivValuedInteger).symm
      (v : (Valued.v.integer : Subring completionField)ˣ), by
    rw [← normUnitEquiv_mem_valuedPrincipalUnits_iff]
    simpa using v.property⟩
  left_inv w := by
    apply Subtype.ext
    exact (normUnitEquivValuedInteger).symm_apply_apply
      (w : (Integers completionField)ˣ)
  right_inv v := by
    apply Subtype.ext
    exact (normUnitEquivValuedInteger).apply_symm_apply
      (v : (Valued.v.integer : Subring completionField)ˣ)
  map_mul' w z := by
    apply Subtype.ext
    exact (normUnitEquivValuedInteger).map_mul
      (w : (Integers completionField)ˣ) (z : (Integers completionField)ˣ)

@[simp] theorem principalUnitsEquivValued_apply
    (w : principalUnits (K := completionField)) :
    ((principalUnitsEquivValued w : valuedPrincipalUnits) :
      (Valued.v.integer : Subring completionField)ˣ) =
      normUnitEquivValuedInteger (w : (Integers completionField)ˣ) := rfl

@[simp] theorem principalUnitsEquivValued_symm_apply
    (w : valuedPrincipalUnits) :
    ((principalUnitsEquivValued.symm w :
        principalUnits (K := completionField)) : (Integers completionField)ˣ) =
      (normUnitEquivValuedInteger).symm
        (w : (Valued.v.integer : Subring completionField)ˣ) := rfl

/-- The only missing premise for the uniform principal-unit exponent: the
concrete adic completion is proper. -/
def CompletionProperSpaceResidual : Prop :=
  Nonempty (ProperSpace completionField)

/-- Conditional principal refinement: if the concrete completion is proper,
every actual integral unit has a positive power in the actual principal-unit
subgroup. -/
theorem exists_principalUnit_power_valued_integer_unit
    (hproper : CompletionProperSpaceResidual)
    (u : (Valued.v.integer : Subring completionField)ˣ) :
    ∃ N : Nat, 0 < N ∧ u ^ N ∈ valuedPrincipalUnits := by
  letI : ProperSpace completionField := hproper.some
  let e : (Integers completionField)ˣ ≃*
      (Valued.v.integer : Subring completionField)ˣ := normUnitEquivValuedInteger
  let w : (Integers completionField)ˣ := e.symm u
  obtain ⟨N, hNpos, hN⟩ :=
    LocalFieldIntegralUnits.exists_uniform_principalUnit_exponent
      (K := completionField)
  refine ⟨N, hNpos, ?_⟩
  rw [valuedPrincipalUnits, Subgroup.mem_comap]
  simpa only [map_pow] using hN ((normUnitEquivValuedInteger).symm u)

/-- Valuation-inequality form of the conditional principal refinement. -/
theorem exists_principalUnit_power_valuation_lt_one
    (hproper : CompletionProperSpaceResidual)
    (u : (Valued.v.integer : Subring completionField)ˣ) :
    ∃ N : Nat, 0 < N ∧
      (Valued.v ((((u ^ N).val).1 : completionField) - 1) :
        WithZero (Multiplicative Int)) < 1 := by
  obtain ⟨N, hNpos, hmem⟩ :=
    exists_principalUnit_power_valued_integer_unit hproper u
  exact ⟨N, hNpos, (mem_valuedPrincipalUnits_iff _).mp hmem⟩

/-- Uniform exponent form for all actual integral units, conditional on
properness. -/
theorem exists_uniform_principalUnit_power_valued
    (hproper : CompletionProperSpaceResidual) :
    ∃ N : Nat, 0 < N ∧
      ∀ u : (Valued.v.integer : Subring completionField)ˣ,
        u ^ N ∈ valuedPrincipalUnits := by
  letI : ProperSpace completionField := hproper.some
  obtain ⟨N, hNpos, hN⟩ :=
    LocalFieldIntegralUnits.exists_uniform_principalUnit_exponent
      (K := completionField)
  refine ⟨N, hNpos, ?_⟩
  intro u
  rw [valuedPrincipalUnits, Subgroup.mem_comap]
  simpa only [map_pow] using hN ((normUnitEquivValuedInteger).symm u)

/-- Conditional DVR decomposition with principal refinement. -/
theorem exists_uniformizer_dvr_principal_refinement
    (hproper : CompletionProperSpaceResidual) (u : completionFieldˣ) :
    ∃ m : Int, ∃ u0 : (Valued.v.integer : Subring completionField)ˣ,
      (u : completionField) = concreteAdicUniformizer ^ m *
        ((u0.val).1 : completionField) ∧
      ∃ N : Nat, 0 < N ∧ u0 ^ N ∈ valuedPrincipalUnits := by
  obtain ⟨m, u0, hdec⟩ := exists_uniformizer_dvr_decomposition u
  obtain ⟨N, hNpos, hprin⟩ :=
    exists_principalUnit_power_valued_integer_unit hproper u0
  exact ⟨m, u0, hdec, N, hNpos, hprin⟩

/-- DVR decomposition with principal refinement in valuation-inequality form. -/
theorem exists_uniformizer_dvr_valuation_refinement
    (hproper : CompletionProperSpaceResidual) (u : completionFieldˣ) :
    ∃ m : Int, ∃ u0 : (Valued.v.integer : Subring completionField)ˣ,
      (u : completionField) = concreteAdicUniformizer ^ m *
        ((u0.val).1 : completionField) ∧
      ∃ N : Nat, 0 < N ∧
        (Valued.v ((((u0 ^ N).val).1 : completionField) - 1) :
          WithZero (Multiplicative Int)) < 1 := by
  obtain ⟨m, u0, hdec⟩ := exists_uniformizer_dvr_decomposition u
  obtain ⟨N, hNpos, hval⟩ :=
    exists_principalUnit_power_valuation_lt_one hproper u0
  exact ⟨m, u0, hdec, N, hNpos, hval⟩

/-- DVR decomposition with the integral part in the normalized norm unit ball. -/
theorem exists_uniformizer_dvr_norm_unit_decomposition
    (hproper : CompletionProperSpaceResidual) (u : completionFieldˣ) :
    ∃ m : Int, ∃ u0 : (Integers completionField)ˣ,
      (u : completionField) = concreteAdicUniformizer ^ m *
        ((u0 : (Integers completionField)) : completionField) ∧
      ∃ N : Nat, 0 < N ∧ u0 ^ N ∈ principalUnits (K := completionField) := by
  obtain ⟨m, u0, hdec⟩ := exists_uniformizer_dvr_decomposition u
  let w : (Integers completionField)ˣ := (normUnitEquivValuedInteger).symm u0
  have hcoe : ((w : (Integers completionField)) : completionField) =
      ((u0.val).1 : completionField) := rfl
  obtain ⟨N, hNpos, hprin⟩ :=
    exists_principalUnit_power_valued_integer_unit hproper u0
  have hmap : normUnitEquivValuedInteger (w ^ N) = u0 ^ N := by
    dsimp [w]
    rw [map_pow, MulEquiv.apply_symm_apply]
  have hprincipal : w ^ N ∈ principalUnits (K := completionField) :=
    (normUnitEquiv_mem_valuedPrincipalUnits_iff (w ^ N)).mp (by rwa [hmap])
  exact ⟨m, w, by rw [hcoe]; exact hdec, N, hNpos, hprincipal⟩

/-- The actual principal-unit subgroup is closed under powers. -/
theorem valuedPrincipalUnits_pow_mem
    {u : (Valued.v.integer : Subring completionField)ˣ}
    (hu : u ∈ valuedPrincipalUnits) (n : Nat) :
    u ^ n ∈ valuedPrincipalUnits :=
  valuedPrincipalUnits.pow_mem hu n

theorem valuedPrincipalUnits_inv_mem
    {u : (Valued.v.integer : Subring completionField)ˣ}
    (hu : u ∈ valuedPrincipalUnits) :
    u⁻¹ ∈ valuedPrincipalUnits :=
  valuedPrincipalUnits.inv_mem hu

theorem valuedPrincipalUnits_mul_mem
    {u v : (Valued.v.integer : Subring completionField)ˣ}
    (hu : u ∈ valuedPrincipalUnits) (hv : v ∈ valuedPrincipalUnits) :
    u * v ∈ valuedPrincipalUnits :=
  valuedPrincipalUnits.mul_mem hu hv

end LeanFormal.IUT.NormalizedLogNormConsumer
