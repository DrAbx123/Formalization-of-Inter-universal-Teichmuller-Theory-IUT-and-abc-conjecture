import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackend
import LeanFormal.IUT.IUTII.Frobenioid.Example36ArchimedeanLocal
import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalIdealValuation
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Perfect
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Tactic

/-!
# The actual local Galois-invariant monoid at finite and infinite places

This file is the Layer-1 handoff Ch1 §J2 construction.  For a valued local
field `K` (in the application `K = v.adicCompletion F` at a finite place of a
number field `F`) we take the actual integral monoid
`(Valued.integer K)⁰`, its integral closure
`integralClosure (Valued.integer K) (AlgebraicClosure K)`, and the actual
action of the absolute Galois group `Gal(AlgebraicClosure K/K)`.  The fixed
submonoid is proved to be exactly the image of the actual valuation ring
`Valued.integer K`, and the induced monoid map is a multiplicative
equivalence onto the fixed submonoid.

At an archimedean place the local field is `ℝ` or `ℂ`; the closed unit ball
and the norm-one unit subgroup are the archimedean analogue, formalized in
`Example36ArchimedeanLocal`.  The finite-place identification below does not
depend on that analogue.

## The unit group and the value kernel

The same argument at the level of units identifies the Galois-invariant units
of the integral closure with the units `O_K^×` of the valuation ring
(`finitePlaceGaloisInvariantUnitSubgroup_eq_range`, with the multiplicative
equivalence `finitePlaceIntegralUnitsEquivGaloisInvariantUnits`); the
invariant units of the ambient algebraic closure are exactly `K^×`
(`absoluteGaloisInvariantUnitSubgroup_eq_baseFieldUnits`).  In valuation
terms, the units of `O_K` are exactly the value kernel `v^{-1}(1)`
(`finitePlaceIntegralUnits_valuation_eq_one`,
`finitePlaceIntegralUnits_range_eq_valuation_one`), so the invariant units of
the integral closure *are* the value-kernel units of the local field.

The value-group level statement (the fixed subgroup of the value group of a
Galois-invariant extension of the valuation, identified with the base value
group) is not proved: it requires the extension of `Valued.v` to the
algebraic closure, which is not constructed in the tree and is not assumed
here.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36
namespace LocalGaloisInvariantMonoid

open scoped NumberField WithZero nonZeroDivisors
open IsDedekindDomain

/-! ## 0. The algebraic closure is a Galois extension -/

/-- For a perfect field `K`, the algebraic closure is a Galois extension of
`K`.  This is the actual infinite Galois extension whose automorphism group is
the absolute Galois group. -/
theorem algebraicClosure_isGalois (K : Type*) [Field K] [PerfectField K] :
    IsGalois K (AlgebraicClosure K) where
  to_isSeparable := inferInstance
  to_normal := by
    rw [normal_iff]
    intro x
    exact ⟨Algebra.IsIntegral.isIntegral x, IsAlgClosed.splits _⟩

/-- Fixed points of the absolute Galois group are exactly the base field. -/
theorem algebraicClosure_fixed_iff_mem_range (K : Type*) [Field K] [PerfectField K]
    (x : AlgebraicClosure K) :
    (∀ σ : Gal(AlgebraicClosure K/K), σ x = x) ↔
      x ∈ Set.range (algebraMap K (AlgebraicClosure K)) := by
  letI : IsGalois K (AlgebraicClosure K) := algebraicClosure_isGalois K
  exact (InfiniteGalois.mem_range_algebraMap_iff_fixed x).symm

/-! ## 1. The finite-place integral monoid and its Galois action -/

/-- The actual local integral monoid at a finite place: the nonzero elements of
the valuation ring of the valued local field. -/
abbrev FinitePlaceIntegralMonoid (K : Type*) [Field K] [Valued K ℤᵐ⁰] : Type _ :=
  (Valued.integer K)⁰

/-- The actual integral closure of the local valuation ring in the algebraic
closure of the local field.  This is the ring on which the local absolute Galois
group acts. -/
abbrev LocalIntegralClosure (K : Type*) [Field K] [Valued K ℤᵐ⁰] : Type _ :=
  integralClosure (Valued.integer K) (AlgebraicClosure K)

/-- The actual action of the local absolute Galois group on the integral
closure of the valuation ring. -/
noncomputable def galoisActionOnIntegralClosure (K : Type*) [Field K] [Valued K ℤᵐ⁰]
    (σ : Gal(AlgebraicClosure K/K)) :
    LocalIntegralClosure K ≃ₐ[Valued.integer K] LocalIntegralClosure K :=
  (σ.restrictScalars (Valued.integer K)).mapIntegralClosure

@[simp]
theorem galoisActionOnIntegralClosure_coe (K : Type*) [Field K] [Valued K ℤᵐ⁰]
    (σ : Gal(AlgebraicClosure K/K)) (x : LocalIntegralClosure K) :
    (galoisActionOnIntegralClosure K σ x : AlgebraicClosure K) = σ (x : AlgebraicClosure K) :=
  rfl

/-- The induced action on the nonzero integral elements. -/
noncomputable def galoisActionOnIntegralMonoid (K : Type*) [Field K] [Valued K ℤᵐ⁰]
    (σ : Gal(AlgebraicClosure K/K)) :
    MulAut ((LocalIntegralClosure K)⁰) where
  toFun x :=
    ⟨galoisActionOnIntegralClosure K σ x.1,
      mem_nonZeroDivisors_of_ne_zero (by
        intro h
        apply nonZeroDivisors.coe_ne_zero x
        apply (galoisActionOnIntegralClosure K σ).injective
        simpa using h)⟩
  invFun x :=
    ⟨(galoisActionOnIntegralClosure K σ).symm x.1,
      mem_nonZeroDivisors_of_ne_zero (by
        intro h
        apply nonZeroDivisors.coe_ne_zero x
        apply (galoisActionOnIntegralClosure K σ).symm.injective
        simpa using h)⟩
  left_inv x := by
    apply Subtype.ext
    exact (galoisActionOnIntegralClosure K σ).left_inv x.1
  right_inv x := by
    apply Subtype.ext
    exact (galoisActionOnIntegralClosure K σ).right_inv x.1
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (galoisActionOnIntegralClosure K σ) x.1 y.1

/-- The submonoid of local integral elements invariant under the actual local
Galois action. -/
noncomputable def finitePlaceGaloisInvariantMonoid (K : Type*) [Field K] [Valued K ℤᵐ⁰] :
    Submonoid ((LocalIntegralClosure K)⁰) where
  carrier := {x | ∀ σ : Gal(AlgebraicClosure K/K), galoisActionOnIntegralMonoid K σ x = x}
  one_mem' := by
    intro σ
    apply Subtype.ext
    exact map_one (galoisActionOnIntegralClosure K σ)
  mul_mem' := by
    intro x y hx hy σ
    rw [map_mul, hx σ, hy σ]

@[simp]
theorem mem_finitePlaceGaloisInvariantMonoid_iff (K : Type*) [Field K] [Valued K ℤᵐ⁰]
    (x : (LocalIntegralClosure K)⁰) :
    x ∈ finitePlaceGaloisInvariantMonoid K ↔
      ∀ σ : Gal(AlgebraicClosure K/K), galoisActionOnIntegralMonoid K σ x = x :=
  Iff.rfl

/-- Injectivity of the actual map from the valuation ring into the algebraic
closure.  This is not an instance-level `algebraMap` injectivity fact: the
source is a valuation ring rather than a field, so the proof uses the
factorization through the fraction field `K`. -/
theorem algebraMap_valuedInteger_algebraicClosure_injective
    (K : Type*) [Field K] [Valued K ℤᵐ⁰] :
    Function.Injective (algebraMap (Valued.integer K) (AlgebraicClosure K)) := by
  intro x y h
  apply Subtype.ext
  apply (algebraMap K (AlgebraicClosure K)).injective
  rw [IsScalarTower.algebraMap_apply (Valued.integer K) K (AlgebraicClosure K),
    IsScalarTower.algebraMap_apply (Valued.integer K) K (AlgebraicClosure K)] at h
  exact h

/-- The actual valuation ring included in its integral closure. -/
noncomputable def finitePlaceIntegralMonoidToClosure (K : Type*) [Field K] [Valued K ℤᵐ⁰] :
    FinitePlaceIntegralMonoid K →* (LocalIntegralClosure K)⁰ where
  toFun x :=
    ⟨⟨algebraMap (Valued.integer K) (AlgebraicClosure K) x.1,
        algebraMap_mem (integralClosure (Valued.integer K) (AlgebraicClosure K)) x.1⟩,
      mem_nonZeroDivisors_of_ne_zero (by
        intro h
        apply nonZeroDivisors.coe_ne_zero x
        apply algebraMap_valuedInteger_algebraicClosure_injective K
        have h' : algebraMap (Valued.integer K) (AlgebraicClosure K) x.1 =
            ((0 : LocalIntegralClosure K) : AlgebraicClosure K) := by
          simpa only [Subtype.coe_mk] using
            congrArg (fun z : LocalIntegralClosure K => (z : AlgebraicClosure K)) h
        change algebraMap (Valued.integer K) (AlgebraicClosure K) x.1 =
          (0 : AlgebraicClosure K) at h'
        simpa using h')⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact map_one _
  map_mul' := by
    intro x y
    apply Subtype.ext
    apply Subtype.ext
    exact map_mul _ x.1 y.1

@[simp]
theorem finitePlaceIntegralMonoidToClosure_apply (K : Type*) [Field K] [Valued K ℤᵐ⁰]
    (x : FinitePlaceIntegralMonoid K) :
    (((finitePlaceIntegralMonoidToClosure K x : (LocalIntegralClosure K)⁰) :
        LocalIntegralClosure K) : AlgebraicClosure K) =
      algebraMap (Valued.integer K) (AlgebraicClosure K) x.1 :=
  rfl

/-- The fixed submonoid is exactly the image of the actual valuation ring. -/
theorem finitePlaceGaloisInvariantMonoid_mem_iff_exists_base
    (K : Type*) [Field K] [PerfectField K] [Valued K ℤᵐ⁰]
    (x : (LocalIntegralClosure K)⁰) :
    x ∈ finitePlaceGaloisInvariantMonoid K ↔
      ∃ y : FinitePlaceIntegralMonoid K, finitePlaceIntegralMonoidToClosure K y = x := by
  constructor
  · intro hx
    have hfix : ∀ σ : Gal(AlgebraicClosure K/K), σ x.1.1 = x.1.1 := by
      intro σ
      have h := congrArg (fun z : (LocalIntegralClosure K)⁰ =>
        (z.1.1 : AlgebraicClosure K)) (hx σ)
      simpa [galoisActionOnIntegralMonoid, galoisActionOnIntegralClosure_coe] using h
    letI : IsGalois K (AlgebraicClosure K) := algebraicClosure_isGalois K
    obtain ⟨y, hy⟩ :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) x.1.1).mpr hfix
    have hint : IsIntegral (Valued.integer K) (x.1.1 : AlgebraicClosure K) :=
      IsIntegralClosure.isIntegral_iff.mpr ⟨x.1, rfl⟩
    have hint_y : IsIntegral (Valued.integer K) y := by
      apply (isIntegral_algebraMap_iff (algebraMap K (AlgebraicClosure K)).injective).mp
      rwa [← hy] at hint
    obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (K := K)).mp hint_y
    have hz_ne : z ≠ 0 := by
      intro hz0
      apply nonZeroDivisors.coe_ne_zero x
      apply Subtype.ext
      have hx0 : (x.1.1 : AlgebraicClosure K) = 0 := by
        rw [← hy, ← hz, hz0]
        exact map_zero _
      exact hx0
    refine ⟨⟨z, mem_nonZeroDivisors_of_ne_zero hz_ne⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [finitePlaceIntegralMonoidToClosure_apply,
      IsScalarTower.algebraMap_apply (Valued.integer K) K (AlgebraicClosure K), hz, hy]
  · rintro ⟨y, rfl⟩
    intro σ
    apply Subtype.ext
    apply Subtype.ext
    change (galoisActionOnIntegralClosure K σ
      (finitePlaceIntegralMonoidToClosure K y).1 : AlgebraicClosure K) = _
    rw [galoisActionOnIntegralClosure_coe, finitePlaceIntegralMonoidToClosure_apply,
      IsScalarTower.algebraMap_apply (Valued.integer K) K (AlgebraicClosure K)]
    exact σ.commutes (algebraMap (Valued.integer K) K y.1)

/-! ## 2. The monoid identification -/

/-- The actual integral monoid maps injectively into its integral closure. -/
theorem finitePlaceIntegralMonoidToClosure_injective
    (K : Type*) [Field K] [Valued K ℤᵐ⁰] :
    Function.Injective (finitePlaceIntegralMonoidToClosure K) := by
  intro x y h
  have h' : algebraMap (Valued.integer K) (AlgebraicClosure K) x.1 =
      algebraMap (Valued.integer K) (AlgebraicClosure K) y.1 := by
    simpa only [finitePlaceIntegralMonoidToClosure_apply] using
      congrArg (fun z : (LocalIntegralClosure K)⁰ => (z.1.1 : AlgebraicClosure K)) h
  exact Subtype.ext (algebraMap_valuedInteger_algebraicClosure_injective K h')

/-- The range of the integral monoid is exactly the Galois-fixed submonoid. -/
theorem finitePlaceIntegralMonoidToClosure_mrange
    (K : Type*) [Field K] [PerfectField K] [Valued K ℤᵐ⁰] :
    MonoidHom.mrange (finitePlaceIntegralMonoidToClosure K) =
      finitePlaceGaloisInvariantMonoid K := by
  ext x
  rw [MonoidHom.mem_mrange, finitePlaceGaloisInvariantMonoid_mem_iff_exists_base]

/-- The actual local integral monoid is multiplicatively equivalent to the
Galois-invariant submonoid of the integral closure.  This is the constructive
identification, not merely an equality of underlying sets. -/
noncomputable def finitePlaceIntegralMonoidEquivGaloisInvariant
    (K : Type*) [Field K] [PerfectField K] [Valued K ℤᵐ⁰] :
    FinitePlaceIntegralMonoid K ≃* finitePlaceGaloisInvariantMonoid K :=
  (MulEquiv.ofBijective
    (MonoidHom.mrangeRestrict (finitePlaceIntegralMonoidToClosure K))
    ⟨by
      intro x y h
      apply finitePlaceIntegralMonoidToClosure_injective K
      simpa only [MonoidHom.coe_mrangeRestrict] using congrArg Subtype.val h,
     MonoidHom.mrangeRestrict_surjective (finitePlaceIntegralMonoidToClosure K)⟩).trans
    (MulEquiv.submonoidCongr (finitePlaceIntegralMonoidToClosure_mrange K))

@[simp]
theorem finitePlaceIntegralMonoidEquivGaloisInvariant_apply
    (K : Type*) [Field K] [PerfectField K] [Valued K ℤᵐ⁰]
    (x : FinitePlaceIntegralMonoid K) :
    ((finitePlaceIntegralMonoidEquivGaloisInvariant K x : finitePlaceGaloisInvariantMonoid K) :
        (LocalIntegralClosure K)⁰) = finitePlaceIntegralMonoidToClosure K x :=
  rfl



/-! ## 3. The Galois-invariant units of the integral closure

The fixed submonoid of section 1 has a unit group: the elements of the
integral closure that are units of the integral closure and are fixed by the
local absolute Galois group.  This group is identified with the unit group
`O_K^×` of the valuation ring; equivalently (see
`finitePlaceIntegralUnits_range_eq_valuation_one`) with the value-kernel units
of the local field, i.e. the units of valuation one. -/

/-- The action of the local absolute Galois group on the units of the integral
closure, transported from the action on the integral closure. -/
noncomputable def galoisActionOnIntegralClosureUnits (K : Type*) [Field K] [Valued K ℤᵐ⁰]
    (σ : Gal(AlgebraicClosure K/K)) : MulAut ((LocalIntegralClosure K)ˣ) :=
  Units.mapEquiv (galoisActionOnIntegralClosure K σ).toRingEquiv.toMulEquiv

/-- The unit action is the ring action on the underlying integral elements. -/
theorem galoisActionOnIntegralClosureUnits_apply (K : Type*) [Field K] [Valued K ℤᵐ⁰]
    (σ : Gal(AlgebraicClosure K/K)) (u : (LocalIntegralClosure K)ˣ) :
    ((galoisActionOnIntegralClosureUnits K σ u : (LocalIntegralClosure K)ˣ) :
        LocalIntegralClosure K) = galoisActionOnIntegralClosure K σ (u : LocalIntegralClosure K) :=
  rfl

/-- The action on the underlying element of the integral closure, in the
monoid-homomorphism form used for the fixed subgroup. -/
theorem galoisActionOnIntegralClosureUnits_toMonoidHom_coe
    (K : Type*) [Field K] [Valued K ℤᵐ⁰]
    (σ : Gal(AlgebraicClosure K/K)) (u : (LocalIntegralClosure K)ˣ) :
    ((((galoisActionOnIntegralClosureUnits K σ).toMonoidHom u : (LocalIntegralClosure K)ˣ) :
        LocalIntegralClosure K) : AlgebraicClosure K) =
      σ (((u : LocalIntegralClosure K) : AlgebraicClosure K)) :=
  rfl

/-- The subgroup of local integral units whose underlying integral element is
fixed by the actual local Galois action. -/
noncomputable def finitePlaceGaloisInvariantUnitSubgroup
    (K : Type*) [Field K] [Valued K ℤᵐ⁰] : Subgroup ((LocalIntegralClosure K)ˣ) where
  carrier := {u | ∀ σ : Gal(AlgebraicClosure K/K),
    (galoisActionOnIntegralClosureUnits K σ).toMonoidHom u = u}
  one_mem' := by
    intro σ
    exact map_one _
  mul_mem' := by
    intro u v hu hv σ
    rw [map_mul, hu σ, hv σ]
  inv_mem' := by
    intro u hu σ
    rw [MonoidHom.map_inv, hu σ]

@[simp]
theorem mem_finitePlaceGaloisInvariantUnitSubgroup_iff
    (K : Type*) [Field K] [Valued K ℤᵐ⁰] (u : (LocalIntegralClosure K)ˣ) :
    u ∈ finitePlaceGaloisInvariantUnitSubgroup K ↔
      ∀ σ : Gal(AlgebraicClosure K/K),
        (galoisActionOnIntegralClosureUnits K σ).toMonoidHom u = u :=
  Iff.rfl

/-- The actual unit group of the valuation ring mapped into the units of its
integral closure. -/
noncomputable def finitePlaceIntegralUnitsToClosure
    (K : Type*) [Field K] [Valued K ℤᵐ⁰] :
    (Valued.integer K)ˣ →* (LocalIntegralClosure K)ˣ :=
  Units.map (algebraMap (Valued.integer K) (LocalIntegralClosure K)).toMonoidHom

/-- The unit map is the ring map on representatives. -/
theorem finitePlaceIntegralUnitsToClosure_apply (K : Type*) [Field K] [Valued K ℤᵐ⁰]
    (y : (Valued.integer K)ˣ) :
    ((finitePlaceIntegralUnitsToClosure K y : (LocalIntegralClosure K)ˣ) :
        LocalIntegralClosure K) =
      algebraMap (Valued.integer K) (LocalIntegralClosure K) (y : Valued.integer K) :=
  rfl

/-- The unit map followed by the inclusion of the integral closure is the
algebra map into the algebraic closure. -/
@[simp]
theorem finitePlaceIntegralUnitsToClosure_coe_closure
    (K : Type*) [Field K] [Valued K ℤᵐ⁰] (y : (Valued.integer K)ˣ) :
    (((finitePlaceIntegralUnitsToClosure K y : (LocalIntegralClosure K)ˣ) :
        LocalIntegralClosure K) : AlgebraicClosure K) =
      algebraMap (Valued.integer K) (AlgebraicClosure K) (y : Valued.integer K) := by
  rw [finitePlaceIntegralUnitsToClosure_apply]
  exact IsScalarTower.algebraMap_apply (Valued.integer K) (LocalIntegralClosure K)
    (AlgebraicClosure K) _

/-- The unit map is injective. -/
theorem finitePlaceIntegralUnitsToClosure_injective
    (K : Type*) [Field K] [Valued K ℤᵐ⁰] :
    Function.Injective (finitePlaceIntegralUnitsToClosure K) := by
  intro x y h
  have h' : algebraMap (Valued.integer K) (LocalIntegralClosure K) (x : Valued.integer K) =
      algebraMap (Valued.integer K) (LocalIntegralClosure K) (y : Valued.integer K) := by
    have := congrArg (fun w : (LocalIntegralClosure K)ˣ =>
      (w : LocalIntegralClosure K)) h
    simpa only [finitePlaceIntegralUnitsToClosure_apply] using this
  have h'' : algebraMap (Valued.integer K) (AlgebraicClosure K) (x : Valued.integer K) =
      algebraMap (Valued.integer K) (AlgebraicClosure K) (y : Valued.integer K) := by
    rw [IsScalarTower.algebraMap_apply (Valued.integer K) (LocalIntegralClosure K)
        (AlgebraicClosure K) (x : Valued.integer K),
      IsScalarTower.algebraMap_apply (Valued.integer K) (LocalIntegralClosure K)
        (AlgebraicClosure K) (y : Valued.integer K)]
    exact congrArg (algebraMap (LocalIntegralClosure K) (AlgebraicClosure K)) h'
  exact Units.ext (algebraMap_valuedInteger_algebraicClosure_injective K h'')

/-- The range of the unit map, as an actual subgroup of the units of the
integral closure. -/
noncomputable def finitePlaceIntegralUnitsRangeSubgroup
    (K : Type*) [Field K] [Valued K ℤᵐ⁰] : Subgroup ((LocalIntegralClosure K)ˣ) where
  carrier := Set.range (finitePlaceIntegralUnitsToClosure K)
  one_mem' := ⟨1, map_one _⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, map_mul _ a b⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a⁻¹, MonoidHom.map_inv _ a⟩

@[simp]
theorem mem_finitePlaceIntegralUnitsRangeSubgroup_iff
    (K : Type*) [Field K] [Valued K ℤᵐ⁰] (u : (LocalIntegralClosure K)ˣ) :
    u ∈ finitePlaceIntegralUnitsRangeSubgroup K ↔
      ∃ y : (Valued.integer K)ˣ, finitePlaceIntegralUnitsToClosure K y = u :=
  Iff.rfl

/-- **The fixed units are exactly the units of the valuation ring.** -/
theorem finitePlaceGaloisInvariantUnitSubgroup_eq_range
    (K : Type*) [Field K] [PerfectField K] [Valued K ℤᵐ⁰] :
    finitePlaceGaloisInvariantUnitSubgroup K = finitePlaceIntegralUnitsRangeSubgroup K := by
  ext u
  constructor
  · intro hu
    -- the underlying integral element is fixed
    have hfix : ∀ σ : Gal(AlgebraicClosure K/K),
        σ ((u : LocalIntegralClosure K) : AlgebraicClosure K) =
          ((u : LocalIntegralClosure K) : AlgebraicClosure K) := by
      intro σ
      have h := congrArg (fun w : (LocalIntegralClosure K)ˣ =>
        ((w : LocalIntegralClosure K) : AlgebraicClosure K)) (hu σ)
      rw [galoisActionOnIntegralClosureUnits_toMonoidHom_coe] at h
      exact h
    -- hence it lies in the base field
    letI : IsGalois K (AlgebraicClosure K) := algebraicClosure_isGalois K
    obtain ⟨b, hb⟩ :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K)
        ((u : LocalIntegralClosure K) : AlgebraicClosure K)).mpr hfix
    -- the inverse unit is fixed as well
    have hfixinv : ∀ σ : Gal(AlgebraicClosure K/K),
        σ (((u⁻¹ : (LocalIntegralClosure K)ˣ) : LocalIntegralClosure K) :
          AlgebraicClosure K) =
          (((u⁻¹ : (LocalIntegralClosure K)ˣ) : LocalIntegralClosure K) :
            AlgebraicClosure K) := by
      intro σ
      have h' : (galoisActionOnIntegralClosureUnits K σ).toMonoidHom
          (u⁻¹ : (LocalIntegralClosure K)ˣ) = u⁻¹ := by
        rw [MonoidHom.map_inv, hu σ]
      have h := congrArg (fun w : (LocalIntegralClosure K)ˣ =>
        ((w : LocalIntegralClosure K) : AlgebraicClosure K)) h'
      rw [galoisActionOnIntegralClosureUnits_toMonoidHom_coe] at h
      exact h
    obtain ⟨b', hb'⟩ :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K)
        (((u⁻¹ : (LocalIntegralClosure K)ˣ) : LocalIntegralClosure K) :
          AlgebraicClosure K)).mpr hfixinv
    -- integrality of both
    have hint : IsIntegral (Valued.integer K) b := by
      apply (isIntegral_algebraMap_iff (algebraMap K (AlgebraicClosure K)).injective).mp
      rw [hb]
      exact IsIntegralClosure.isIntegral_iff.mpr ⟨(u : LocalIntegralClosure K), rfl⟩
    have hint' : IsIntegral (Valued.integer K) b' := by
      apply (isIntegral_algebraMap_iff (algebraMap K (AlgebraicClosure K)).injective).mp
      rw [hb']
      exact IsIntegralClosure.isIntegral_iff.mpr
        ⟨((u⁻¹ : (LocalIntegralClosure K)ˣ) : LocalIntegralClosure K), rfl⟩
    -- both lie in the integrally closed valuation ring
    obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (K := K)).mp hint
    obtain ⟨z', hz'⟩ := (IsIntegrallyClosed.isIntegral_iff (K := K)).mp hint'
    -- and they are mutually inverse in the fraction field
    have hbb' : b * b' = 1 := by
      apply (algebraMap K (AlgebraicClosure K)).injective
      rw [map_mul, map_one, hb, hb']
      have h := congrArg (fun w : (LocalIntegralClosure K)ˣ =>
        ((w : LocalIntegralClosure K) : AlgebraicClosure K)) (mul_inv_cancel u)
      rw [Units.val_mul, Units.val_one] at h
      exact h
    have hzz' : z * z' = 1 := by
      apply algebraMap_valuedInteger_algebraicClosure_injective K
      rw [map_mul, map_one, IsScalarTower.algebraMap_apply (Valued.integer K) K
        (AlgebraicClosure K), IsScalarTower.algebraMap_apply (Valued.integer K) K
        (AlgebraicClosure K), hz, hz', ← map_mul, hbb', map_one]
    have hz'z : z' * z = 1 := by
      apply algebraMap_valuedInteger_algebraicClosure_injective K
      rw [map_mul, map_one, IsScalarTower.algebraMap_apply (Valued.integer K) K
        (AlgebraicClosure K), IsScalarTower.algebraMap_apply (Valued.integer K) K
        (AlgebraicClosure K), hz, hz', ← map_mul, mul_comm b' b, hbb', map_one]
    refine ⟨Units.mk z z' hzz' hz'z, ?_⟩
    apply Units.ext
    apply Subtype.ext
    rw [finitePlaceIntegralUnitsToClosure_coe_closure,
      IsScalarTower.algebraMap_apply (Valued.integer K) K (AlgebraicClosure K), hz, hb]
  · rintro ⟨y, rfl⟩
    intro σ
    apply Units.ext
    apply Subtype.ext
    rw [galoisActionOnIntegralClosureUnits_toMonoidHom_coe,
      finitePlaceIntegralUnitsToClosure_coe_closure]
    exact σ.commutes _

/-- **The actual units of the valuation ring are multiplicatively equivalent to
the Galois-invariant units of the integral closure.** -/
noncomputable def finitePlaceIntegralUnitsEquivGaloisInvariantUnits
    (K : Type*) [Field K] [PerfectField K] [Valued K ℤᵐ⁰] :
    (Valued.integer K)ˣ ≃* finitePlaceGaloisInvariantUnitSubgroup K :=
  (MulEquiv.ofBijective
    (MonoidHom.codRestrict (finitePlaceIntegralUnitsToClosure K)
      (finitePlaceIntegralUnitsRangeSubgroup K) (fun y => ⟨y, rfl⟩))
    ⟨by
      intro x y h
      apply finitePlaceIntegralUnitsToClosure_injective K
      exact congrArg Subtype.val h,
     by
      rintro ⟨u, hu⟩
      obtain ⟨y, hy⟩ := hu
      exact ⟨y, Subtype.ext hy⟩⟩).trans
    (MulEquiv.subgroupCongr (finitePlaceGaloisInvariantUnitSubgroup_eq_range K).symm)

@[simp]
theorem finitePlaceIntegralUnitsEquivGaloisInvariantUnits_apply
    (K : Type*) [Field K] [PerfectField K] [Valued K ℤᵐ⁰] (y : (Valued.integer K)ˣ) :
    ((finitePlaceIntegralUnitsEquivGaloisInvariantUnits K y :
        finitePlaceGaloisInvariantUnitSubgroup K) : (LocalIntegralClosure K)ˣ) =
      finitePlaceIntegralUnitsToClosure K y :=
  rfl

/-! ## 4. The invariant units of the ambient field and the value kernel

The local absolute Galois group also acts on the units of the algebraic
closure; the fixed units there are exactly the units of the base local field.
Combined with section 3 this identifies the invariant units of the integral
closure with the value-kernel units of the local field, i.e. the units of
valuation one.

What is *not* proved here (precise remaining proposition): the corresponding
statement at the level of value groups.  It requires an extension of the local
valuation `Valued.v` to the algebraic closure that is invariant under the local
absolute Galois group, together with the identification of the fixed subgroup
of its value group with the value group of the base field.  No such extension
is constructed in the tree, and it is not assumed here; the intrinsic unit-level
statement below is the part that is proved. -/

/-- The action of the local absolute Galois group on the units of the
algebraic closure. -/
noncomputable def galoisActionOnAlgebraicClosureUnits (K : Type*) [Field K]
    (σ : Gal(AlgebraicClosure K/K)) : MulAut ((AlgebraicClosure K)ˣ) :=
  Units.mapEquiv σ.toRingEquiv.toMulEquiv

/-- The action on units is the field action on the underlying elements. -/
theorem galoisActionOnAlgebraicClosureUnits_apply (K : Type*) [Field K]
    (σ : Gal(AlgebraicClosure K/K)) (u : (AlgebraicClosure K)ˣ) :
    ((galoisActionOnAlgebraicClosureUnits K σ u : (AlgebraicClosure K)ˣ) :
        AlgebraicClosure K) = σ (u : AlgebraicClosure K) :=
  rfl

/-- The subgroup of units of the algebraic closure fixed by the local absolute
Galois group. -/
noncomputable def absoluteGaloisInvariantUnitSubgroup
    (K : Type*) [Field K] [PerfectField K] : Subgroup ((AlgebraicClosure K)ˣ) where
  carrier := {u | ∀ σ : Gal(AlgebraicClosure K/K), σ (u : AlgebraicClosure K) = u}
  one_mem' := by
    intro σ
    rw [Units.val_one, map_one]
  mul_mem' := by
    intro u v hu hv σ
    rw [Units.val_mul, map_mul, hu σ, hv σ]
  inv_mem' := by
    intro u hu σ
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu σ]

@[simp]
theorem mem_absoluteGaloisInvariantUnitSubgroup_iff
    (K : Type*) [Field K] [PerfectField K] (u : (AlgebraicClosure K)ˣ) :
    u ∈ absoluteGaloisInvariantUnitSubgroup K ↔
      ∀ σ : Gal(AlgebraicClosure K/K), σ (u : AlgebraicClosure K) = u :=
  Iff.rfl

/-- The range of the base-field unit map, as an actual subgroup of the units of
the algebraic closure. -/
noncomputable def baseFieldUnitsRangeSubgroup (K : Type*) [Field K] :
    Subgroup ((AlgebraicClosure K)ˣ) where
  carrier := Set.range (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom)
  one_mem' := ⟨1, map_one _⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, map_mul _ a b⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨a⁻¹, MonoidHom.map_inv _ a⟩

/-- **The invariant units of the ambient field are the units of the base local
field.** -/
theorem absoluteGaloisInvariantUnitSubgroup_eq_baseFieldUnits
    (K : Type*) [Field K] [PerfectField K] :
    absoluteGaloisInvariantUnitSubgroup K = baseFieldUnitsRangeSubgroup K := by
  ext u
  constructor
  · intro hu
    letI : IsGalois K (AlgebraicClosure K) := algebraicClosure_isGalois K
    obtain ⟨b, hb⟩ :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K)
        (u : AlgebraicClosure K)).mpr (hu ·)
    have hb0 : b ≠ 0 := by
      intro h0
      apply Units.ne_zero u
      rw [← hb, h0, map_zero]
    refine ⟨Units.mk0 b hb0, ?_⟩
    apply Units.ext
    rw [Units.coe_map, Units.val_mk0]
    exact hb
  · rintro ⟨y, rfl⟩
    intro σ
    rw [Units.coe_map]
    exact σ.commutes (y : K)

/-- **The unit group of the valuation ring is the value kernel of the local
valuation**: a unit of the valuation ring has valuation one. -/
theorem finitePlaceIntegralUnits_valuation_eq_one
    (K : Type*) [Field K] [Valued K ℤᵐ⁰] (y : (Valued.integer K)ˣ) :
    Valued.v ((y : Valued.integer K) : K) = 1 :=
  Valuation.Integers.one_of_isUnit (v := Valued.v) (O := Valued.integer K)
    (Valuation.integer.integers (v := Valued.v)) y.isUnit

/-- **The value kernel of the local valuation is the unit group of the
valuation ring**: the units of `K` of valuation one are exactly the images of
the units of `O_K`. -/
theorem finitePlaceIntegralUnits_range_eq_valuation_one
    (K : Type*) [Field K] [Valued K ℤᵐ⁰] :
    (MonoidHom.mrange (Units.map (algebraMap (Valued.integer K) K).toMonoidHom) : Set Kˣ) =
      {x : Kˣ | Valued.v (x : K) = 1} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact finitePlaceIntegralUnits_valuation_eq_one K y
  · intro hx
    have hx1 : Valued.v (x : K) ≤ 1 := le_of_eq hx
    have hx1' : Valued.v (((x⁻¹ : Kˣ) : K)) ≤ 1 := by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hx]
      simp
    refine ⟨Units.mk ⟨(x : K), hx1⟩ ⟨((x⁻¹ : Kˣ) : K), hx1'⟩ ?_ ?_, ?_⟩
    · apply Subtype.ext
      change (x : K) * ((x⁻¹ : Kˣ) : K) = ((1 : (Valued.integer K)) : K)
      rw [Units.val_inv_eq_inv_val]
      simp
    · apply Subtype.ext
      change ((x⁻¹ : Kˣ) : K) * (x : K) = ((1 : (Valued.integer K)) : K)
      rw [Units.val_inv_eq_inv_val]
      simp
    · apply Units.ext
      rfl


/-! ## 5. Infinite places: the archimedean local Galois-invariant monoids

At a real place the local field is `ℝ`, and the local absolute Galois group is
`Gal(ℂ/ℝ)`, with the nontrivial element acting by complex conjugation.  At a
complex place the local field is `ℂ` and the local absolute Galois group is
trivial.  In both cases the integral structure is the closed unit ball, and the
local unit group is the norm-one subgroup. -/

section Archimedean

open scoped ComplexConjugate

/-- The action of the real-place local absolute Galois group
`Gal(ℂ/ℝ)` on the units of the local algebraic closure `ℂ`. -/
noncomputable def realArchimedeanGaloisUnitAction (σ : Gal(ℂ/ℝ)) : MulAut ℂˣ :=
  Units.mapEquiv σ.toRingEquiv.toMulEquiv

/-- Every element of `Gal(ℂ/ℝ)` is the identity or complex conjugation. -/
theorem realArchimedeanGalois_eq_one_or_conj (σ : Gal(ℂ/ℝ)) :
    σ = 1 ∨ σ = Complex.conjAe := by
  have h := Complex.real_algHom_eq_id_or_conj (σ : ℂ →ₐ[ℝ] ℂ)
  rcases h with h | h
  · left
    ext z
    exact congrArg (fun f : ℂ →ₐ[ℝ] ℂ => f z) h
  · right
    ext z
    exact congrArg (fun f : ℂ →ₐ[ℝ] ℂ => f z) h

/-- The action of complex conjugation on the units of `ℂ`. -/
noncomputable def complexConjUnitAction : MulAut ℂˣ :=
  Units.mapEquiv Complex.conjAe.toRingEquiv.toMulEquiv

@[simp]
theorem complexConjUnitAction_apply (u : ℂˣ) :
    ((complexConjUnitAction u : ℂˣ) : ℂ) = conj (u : ℂ) :=
  rfl

/-- The real-place action at conjugation is the conjugation action. -/
theorem realArchimedeanGaloisUnitAction_conj :
    realArchimedeanGaloisUnitAction Complex.conjAe = complexConjUnitAction :=
  rfl

/-- The identity of the real-place Galois group acts trivially. -/
@[simp]
theorem realArchimedeanGaloisUnitAction_one (u : ℂˣ) :
    realArchimedeanGaloisUnitAction (1 : Gal(ℂ/ℝ)) u = u := by
  apply Units.ext
  rfl

/-- Fixedness under the whole real-place Galois group is fixedness under
complex conjugation. -/
theorem realArchimedean_fixed_iff_conj (u : ℂˣ) :
    (∀ σ : Gal(ℂ/ℝ), realArchimedeanGaloisUnitAction σ u = u) ↔
      complexConjUnitAction u = u := by
  constructor
  · intro h
    simpa only [realArchimedeanGaloisUnitAction_conj] using h Complex.conjAe
  · intro h σ
    rcases realArchimedeanGalois_eq_one_or_conj σ with rfl | rfl
    · simp
    · simpa only [realArchimedeanGaloisUnitAction_conj] using h

/-- The closed unit ball of the units of a normed field, as a multiplicative
submonoid.  This is the integral structure at an archimedean place. -/
def closedUnitBallUnits (K : Type*) [NormedField K] : Submonoid Kˣ where
  carrier := {u : Kˣ | ‖(u : K)‖ ≤ 1}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change ‖((u * v : Kˣ) : K)‖ ≤ 1
    rw [Units.val_mul, norm_mul]
    calc
      ‖(u : K)‖ * ‖(v : K)‖ ≤ 1 * 1 :=
        mul_le_mul hu hv (norm_nonneg _) zero_le_one
      _ = 1 := by norm_num

@[simp]
theorem mem_closedUnitBallUnits (K : Type*) [NormedField K] (u : Kˣ) :
    u ∈ closedUnitBallUnits K ↔ ‖(u : K)‖ ≤ 1 :=
  Iff.rfl

/-- The monoid of local units at a real place that are invariant under the
actual local Galois action and lie in the integral closed unit ball. -/
noncomputable def realPlaceGaloisInvariantMonoid : Submonoid ℂˣ where
  carrier := {u | (∀ σ : Gal(ℂ/ℝ), realArchimedeanGaloisUnitAction σ u = u) ∧
    ‖(u : ℂ)‖ ≤ 1}
  one_mem' := by
    constructor
    · intro σ
      exact map_one _
    · simp
  mul_mem' := by
    intro u v hu hv
    constructor
    · intro σ
      rw [map_mul, hu.1 σ, hv.1 σ]
    · rw [Units.val_mul, norm_mul]
      calc
        ‖(u : ℂ)‖ * ‖(v : ℂ)‖ ≤ 1 * 1 :=
          mul_le_mul hu.2 hv.2 (norm_nonneg _) zero_le_one
        _ = 1 := by norm_num

@[simp]
theorem mem_realPlaceGaloisInvariantMonoid (u : ℂˣ) :
    u ∈ realPlaceGaloisInvariantMonoid ↔
      (∀ σ : Gal(ℂ/ℝ), realArchimedeanGaloisUnitAction σ u = u) ∧
        ‖(u : ℂ)‖ ≤ 1 :=
  Iff.rfl

/-- The subgroup of local units at a real place invariant under the actual
local Galois action and of absolute value one. -/
noncomputable def realPlaceGaloisInvariantUnitGroup : Subgroup ℂˣ where
  carrier := {u | (∀ σ : Gal(ℂ/ℝ), realArchimedeanGaloisUnitAction σ u = u) ∧
    ‖(u : ℂ)‖ = 1}
  one_mem' := by
    constructor
    · intro σ
      exact map_one _
    · simp
  mul_mem' := by
    intro u v hu hv
    constructor
    · intro σ
      rw [map_mul, hu.1 σ, hv.1 σ]
    · rw [Units.val_mul, norm_mul, hu.2, hv.2, one_mul]
  inv_mem' := by
    intro u hu
    constructor
    · intro σ
      calc
        realArchimedeanGaloisUnitAction σ u⁻¹ =
            (realArchimedeanGaloisUnitAction σ u)⁻¹ := by simp
        _ = u⁻¹ := by rw [hu.1 σ]
    · rw [Units.val_inv_eq_inv_val, norm_inv, hu.2, inv_one]

@[simp]
theorem mem_realPlaceGaloisInvariantUnitGroup (u : ℂˣ) :
    u ∈ realPlaceGaloisInvariantUnitGroup ↔
      (∀ σ : Gal(ℂ/ℝ), realArchimedeanGaloisUnitAction σ u = u) ∧
        ‖(u : ℂ)‖ = 1 :=
  Iff.rfl

/-- The actual real units included in the complex units. -/
noncomputable def realUnitsToComplexUnits : ℝˣ →* ℂˣ :=
  Units.map Complex.ofRealHom.toMonoidHom

@[simp]
theorem realUnitsToComplexUnits_apply (u : ℝˣ) :
    ((realUnitsToComplexUnits u : ℂˣ) : ℂ) = (u : ℝ) :=
  rfl

/-- The real units map injectively into the complex units. -/
theorem realUnitsToComplexUnits_injective :
    Function.Injective realUnitsToComplexUnits := by
  intro u v h
  apply Units.ext
  apply Complex.ofReal_injective
  exact congrArg (fun w : ℂˣ => (w : ℂ)) h

/-- The real-place invariant monoid is exactly the image of the closed unit ball
of the actual real units. -/
theorem realPlaceGaloisInvariantMonoid_eq_map :
    realPlaceGaloisInvariantMonoid =
      (closedUnitBallUnits ℝ).map realUnitsToComplexUnits := by
  ext u
  constructor
  · intro hu
    have hfix : complexConjUnitAction u = u :=
      (realArchimedean_fixed_iff_conj u).mp hu.1
    have hconj : conj (u : ℂ) = (u : ℂ) := by
      have h := congrArg (fun w : ℂˣ => (w : ℂ)) hfix
      simpa using h
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp hconj
    have hr0 : r ≠ 0 := by
      intro h0
      apply Units.ne_zero u
      rw [hr, h0]
      simp
    refine ⟨Units.mk0 r hr0, ?_, ?_⟩
    · change ‖((Units.mk0 r hr0 : ℝˣ) : ℝ)‖ ≤ 1
      rw [Units.val_mk0]
      have hnorm : ‖(u : ℂ)‖ = ‖r‖ := by
        rw [hr, Complex.norm_real]
      rw [← hnorm]
      exact hu.2
    · apply Units.ext
      rw [realUnitsToComplexUnits_apply, Units.val_mk0]
      exact hr.symm
  · rintro ⟨r, hr, rfl⟩
    constructor
    · intro σ
      apply Units.ext
      change σ (algebraMap ℝ ℂ (r : ℝ)) = algebraMap ℝ ℂ (r : ℝ)
      exact σ.commutes (r : ℝ)
    · rw [realUnitsToComplexUnits_apply, Complex.norm_real, Real.norm_eq_abs]
      simpa [Real.norm_eq_abs] using hr

/-- The real closed-unit-ball units map to the real-place invariant monoid. -/
noncomputable def realUnitsClosedBallToInvariant :
    closedUnitBallUnits ℝ →* realPlaceGaloisInvariantMonoid where
  toFun u :=
    ⟨realUnitsToComplexUnits u, by
      rw [realPlaceGaloisInvariantMonoid_eq_map]
      exact ⟨u, u.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact map_one realUnitsToComplexUnits
  map_mul' := by
    intro x y
    apply Subtype.ext
    exact map_mul realUnitsToComplexUnits (x : ℝˣ) (y : ℝˣ)

theorem realUnitsClosedBallToInvariant_injective :
    Function.Injective realUnitsClosedBallToInvariant := by
  intro x y h
  apply Subtype.ext
  apply realUnitsToComplexUnits_injective
  exact congrArg (fun z : realPlaceGaloisInvariantMonoid => (z : ℂˣ)) h

theorem realUnitsClosedBallToInvariant_surjective :
    Function.Surjective realUnitsClosedBallToInvariant := by
  intro y
  have hy : (y : ℂˣ) ∈ (closedUnitBallUnits ℝ).map realUnitsToComplexUnits := by
    rw [← realPlaceGaloisInvariantMonoid_eq_map]
    exact y.2
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- The real closed-unit-ball monoid is multiplicatively equivalent to the
real-place Galois-invariant monoid. -/
noncomputable def realUnitsClosedBallEquivGaloisInvariant :
    closedUnitBallUnits ℝ ≃* realPlaceGaloisInvariantMonoid :=
  MulEquiv.ofBijective realUnitsClosedBallToInvariant
    ⟨realUnitsClosedBallToInvariant_injective,
      realUnitsClosedBallToInvariant_surjective⟩

@[simp]
theorem realUnitsClosedBallEquivGaloisInvariant_apply
    (u : closedUnitBallUnits ℝ) :
    ((realUnitsClosedBallEquivGaloisInvariant u : realPlaceGaloisInvariantMonoid) :
        ℂˣ) = realUnitsToComplexUnits u :=
  rfl

/-- The real-place invariant unit group is exactly the image of the actual
norm-one real units. -/
theorem realPlaceGaloisInvariantUnitGroup_eq_map :
    realPlaceGaloisInvariantUnitGroup =
      (normOneUnits ℝ).map realUnitsToComplexUnits := by
  ext u
  constructor
  · intro hu
    have hfix : complexConjUnitAction u = u :=
      (realArchimedean_fixed_iff_conj u).mp hu.1
    have hconj : conj (u : ℂ) = (u : ℂ) := by
      have h := congrArg (fun w : ℂˣ => (w : ℂ)) hfix
      simpa using h
    obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.mp hconj
    have hr0 : r ≠ 0 := by
      intro h0
      apply Units.ne_zero u
      rw [hr, h0]
      simp
    refine ⟨Units.mk0 r hr0, ?_, ?_⟩
    · change ‖((Units.mk0 r hr0 : ℝˣ) : ℝ)‖ = 1
      rw [Units.val_mk0]
      have hnorm : ‖(u : ℂ)‖ = ‖r‖ := by
        rw [hr, Complex.norm_real]
      rw [← hnorm]
      exact hu.2
    · apply Units.ext
      rw [realUnitsToComplexUnits_apply, Units.val_mk0]
      exact hr.symm
  · rintro ⟨r, hr, rfl⟩
    constructor
    · intro σ
      apply Units.ext
      change σ (algebraMap ℝ ℂ (r : ℝ)) = algebraMap ℝ ℂ (r : ℝ)
      exact σ.commutes (r : ℝ)
    · rw [realUnitsToComplexUnits_apply, Complex.norm_real, Real.norm_eq_abs]
      simpa [Real.norm_eq_abs] using (LeanFormal.IUT.mem_normOneUnits (K := ℝ) r).mp hr

/-- The actual norm-one real units map to the real-place invariant unit group. -/
noncomputable def realNormOneUnitsToInvariant :
    normOneUnits ℝ →* realPlaceGaloisInvariantUnitGroup where
  toFun u :=
    ⟨realUnitsToComplexUnits u, by
      rw [realPlaceGaloisInvariantUnitGroup_eq_map]
      exact ⟨u, u.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact map_one realUnitsToComplexUnits
  map_mul' := by
    intro x y
    apply Subtype.ext
    exact map_mul realUnitsToComplexUnits (x : ℝˣ) (y : ℝˣ)

theorem realNormOneUnitsToInvariant_injective :
    Function.Injective realNormOneUnitsToInvariant := by
  intro x y h
  apply Subtype.ext
  apply realUnitsToComplexUnits_injective
  exact congrArg (fun z : realPlaceGaloisInvariantUnitGroup => (z : ℂˣ)) h

theorem realNormOneUnitsToInvariant_surjective :
    Function.Surjective realNormOneUnitsToInvariant := by
  intro y
  have hy : (y : ℂˣ) ∈ (normOneUnits ℝ).map realUnitsToComplexUnits := by
    rw [← realPlaceGaloisInvariantUnitGroup_eq_map]
    exact y.2
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- The actual norm-one real units are multiplicatively equivalent to the
real-place Galois-invariant unit group. -/
noncomputable def realNormOneUnitsEquivGaloisInvariant :
    normOneUnits ℝ ≃* realPlaceGaloisInvariantUnitGroup :=
  MulEquiv.ofBijective realNormOneUnitsToInvariant
    ⟨realNormOneUnitsToInvariant_injective,
      realNormOneUnitsToInvariant_surjective⟩

/-- At a complex place the local absolute Galois group is trivial. -/
theorem complexArchimedeanGalois_eq_one (σ : Gal(ℂ/ℂ)) : σ = 1 := by
  ext z
  simpa using σ.commutes z

/-- The complex unit action at a complex place. -/
noncomputable def complexArchimedeanGaloisUnitAction (σ : Gal(ℂ/ℂ)) : MulAut ℂˣ :=
  Units.mapEquiv σ.toRingEquiv.toMulEquiv

@[simp]
theorem complexArchimedeanGaloisUnitAction_one (u : ℂˣ) :
    complexArchimedeanGaloisUnitAction (1 : Gal(ℂ/ℂ)) u = u := by
  apply Units.ext
  rfl

/-- The monoid of local units at a complex place invariant under the (trivial)
local Galois action and lying in the integral closed unit ball. -/
noncomputable def complexPlaceGaloisInvariantMonoid : Submonoid ℂˣ where
  carrier := {u | (∀ σ : Gal(ℂ/ℂ), complexArchimedeanGaloisUnitAction σ u = u) ∧
    ‖(u : ℂ)‖ ≤ 1}
  one_mem' := by
    constructor
    · intro σ
      exact map_one _
    · simp
  mul_mem' := by
    intro u v hu hv
    constructor
    · intro σ
      rw [map_mul, hu.1 σ, hv.1 σ]
    · rw [Units.val_mul, norm_mul]
      calc
        ‖(u : ℂ)‖ * ‖(v : ℂ)‖ ≤ 1 * 1 :=
          mul_le_mul hu.2 hv.2 (norm_nonneg _) zero_le_one
        _ = 1 := by norm_num

/-- At a complex place the Galois-invariant monoid is the whole closed unit
ball, because the local absolute Galois group is trivial. -/
theorem complexPlaceGaloisInvariantMonoid_eq_closedUnitBall :
    complexPlaceGaloisInvariantMonoid = closedUnitBallUnits ℂ := by
  ext u
  constructor
  · intro hu
    exact hu.2
  · intro hu
    refine ⟨?_, hu⟩
    intro σ
    rw [complexArchimedeanGalois_eq_one σ]
    simp

/-- The subgroup of local units at a complex place invariant under the trivial
local Galois action and of absolute value one. -/
noncomputable def complexPlaceGaloisInvariantUnitGroup : Subgroup ℂˣ where
  carrier := {u | (∀ σ : Gal(ℂ/ℂ), complexArchimedeanGaloisUnitAction σ u = u) ∧
    ‖(u : ℂ)‖ = 1}
  one_mem' := by
    constructor
    · intro σ
      exact map_one _
    · simp
  mul_mem' := by
    intro u v hu hv
    constructor
    · intro σ
      rw [map_mul, hu.1 σ, hv.1 σ]
    · rw [Units.val_mul, norm_mul, hu.2, hv.2, one_mul]
  inv_mem' := by
    intro u hu
    constructor
    · intro σ
      calc
        complexArchimedeanGaloisUnitAction σ u⁻¹ =
            (complexArchimedeanGaloisUnitAction σ u)⁻¹ := by simp
        _ = u⁻¹ := by rw [hu.1 σ]
    · rw [Units.val_inv_eq_inv_val, norm_inv, hu.2, inv_one]

/-- At a complex place the Galois-invariant unit group is the actual norm-one
unit circle. -/
theorem complexPlaceGaloisInvariantUnitGroup_eq_normOneUnits :
    complexPlaceGaloisInvariantUnitGroup = normOneUnits ℂ := by
  ext u
  constructor
  · intro hu
    exact hu.2
  · intro hu
    refine ⟨?_, hu⟩
    intro σ
    rw [complexArchimedeanGalois_eq_one σ]
    simp

end Archimedean

end LocalGaloisInvariantMonoid
end Example36
end LeanFormal.IUT.IUTII.Frobenioid
