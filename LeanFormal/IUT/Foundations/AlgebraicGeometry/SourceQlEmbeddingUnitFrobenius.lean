import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlEmbeddingIntegralUnits
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-!
# Actual l.value-power Frobenius on integral units and the Q_l embedding

This file proves the unit-level p-power Frobenius compatibility for the actual
isometric embedding Q_l -> F_v at p = l.value.  It uses the exact integral-unit
image of SourceQlEmbeddingIntegralUnits.

The source unit Frobenius is u |-> u^l.value, the target unit Frobenius is
v |-> v^l.value, and the embedding intertwines them exactly.  Iterates give the
(l.value)^n-power law.  Principal units are preserved, and the integral-unit
image is stable under the target Frobenius.

No theta spec or alias is used.
-/

namespace ABCBridge.SourceQlEmbeddingUnitFrobenius

noncomputable section

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open ABCBridge.SourceQlEmbeddingConsumer
open ABCBridge.SourceQlEmbeddingIntegralUnits
open scoped NumberField

variable {F : Type} [Field F] [NumberField F]
variable (l : LeanFormal.IUT.PrimeGeFive)
variable (place : FinitePlaceAtPrime F l.value)

local instance sourceQlUnitFrobeniusPrimeFact : Fact (Nat.Prime l.value) :=
  l.factPrime

/-- The actual l.value-power Frobenius on source integral units. -/
noncomputable def sourceQlIntegralUnitFrobenius :
    (Integers (sourceLocalField l))ˣ → (Integers (sourceLocalField l))ˣ :=
  fun u => u ^ l.value

/-- The actual l.value-power Frobenius on target integral units. -/
noncomputable def targetQlIntegralUnitFrobenius :
    (Integers (CommonPrimeCompletion place))ˣ →
      (Integers (CommonPrimeCompletion place))ˣ :=
  fun v => v ^ l.value

@[simp] theorem sourceQlIntegralUnitFrobenius_apply
    (u : (Integers (sourceLocalField l))ˣ) :
    sourceQlIntegralUnitFrobenius l u = u ^ l.value := rfl

@[simp] theorem targetQlIntegralUnitFrobenius_apply
    (v : (Integers (CommonPrimeCompletion place))ˣ) :
    targetQlIntegralUnitFrobenius place v = v ^ l.value := rfl

/-- The unit embedding intertwines the two l.value-power Frobenius maps. -/
theorem sourceQlEmbeddingUnitMap_frobenius
    (u : (Integers (sourceLocalField l))ˣ) :
    sourceQlEmbeddingUnitMap l place
        (sourceQlIntegralUnitFrobenius l u) =
      targetQlIntegralUnitFrobenius place
        (sourceQlEmbeddingUnitMap l place u) := by
  simp [sourceQlIntegralUnitFrobenius, targetQlIntegralUnitFrobenius,
    map_pow]

/-- Iterated source Frobenius is the (l.value)^n-power map. -/
theorem sourceQlIntegralUnitFrobenius_iterate
    (u : (Integers (sourceLocalField l))ˣ) (n : ℕ) :
    (sourceQlIntegralUnitFrobenius l^[n]) u =
      u ^ (l.value ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, sourceQlIntegralUnitFrobenius_apply,
        ← pow_mul]
      rfl

/-- Iterated target Frobenius is the (l.value)^n-power map. -/
theorem targetQlIntegralUnitFrobenius_iterate
    (v : (Integers (CommonPrimeCompletion place))ˣ) (n : ℕ) :
    (targetQlIntegralUnitFrobenius place^[n]) v =
      v ^ (l.value ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, targetQlIntegralUnitFrobenius_apply,
        ← pow_mul]
      rfl

/-- Iterated Frobenius compatibility: the embedding intertwines the n-fold
Frobenius maps for every n. -/
theorem sourceQlEmbeddingUnitMap_frobenius_iterate
    (u : (Integers (sourceLocalField l))ˣ) (n : ℕ) :
    sourceQlEmbeddingUnitMap l place
        ((sourceQlIntegralUnitFrobenius l^[n]) u) =
      (targetQlIntegralUnitFrobenius place^[n])
        (sourceQlEmbeddingUnitMap l place u) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (sourceQlEmbeddingUnitMap_frobenius l place _).trans
        (congrArg (targetQlIntegralUnitFrobenius place) (ih u))

/-- Source principal units are preserved by the l.value-power Frobenius. -/
theorem sourceQlIntegralUnitFrobenius_mem_principalUnits
    (u : (Integers (sourceLocalField l))ˣ) (hu : u ∈ principalUnits) :
    sourceQlIntegralUnitFrobenius l u ∈ principalUnits :=
  (principalUnits (K := sourceLocalField l)).pow_mem hu l.value

/-- Target principal units are preserved by the target l.value-power Frobenius. -/
theorem targetQlIntegralUnitFrobenius_mem_principalUnits
    (v : (Integers (CommonPrimeCompletion place))ˣ) (hv : v ∈ principalUnits) :
    targetQlIntegralUnitFrobenius place v ∈ principalUnits :=
  (principalUnits (K := CommonPrimeCompletion place)).pow_mem hv l.value

/-- The exact integral-unit image is stable under the target l.value-power
Frobenius. -/
theorem sourceQlEmbeddingIntegralUnitImage_frobenius_mem
    (v : sourceQlEmbeddingIntegralUnitImage l place) :
    targetQlIntegralUnitFrobenius place v ∈
      sourceQlEmbeddingIntegralUnitImage l place := by
  obtain ⟨u, rfl⟩ :=
    sourceQlEmbeddingIntegralUnitImage_exists_preimage l place v
  exact ⟨sourceQlIntegralUnitFrobenius l u,
    sourceQlEmbeddingUnitMap_frobenius l place u⟩

/-- The principal-unit image is stable under the target l.value-power
Frobenius. -/
theorem sourceQlEmbeddingPrincipalUnitImage_frobenius_mem
    (v : sourceQlEmbeddingPrincipalUnitImage l place) :
    targetQlIntegralUnitFrobenius place v ∈
      sourceQlEmbeddingPrincipalUnitImage l place := by
  obtain ⟨u, hu, rfl⟩ :=
    (sourceQlEmbeddingPrincipalUnitImage_mem_iff l place v).mp v.property
  exact (Subgroup.mem_map).mpr
    ⟨sourceQlIntegralUnitFrobenius l u,
      sourceQlIntegralUnitFrobenius_mem_principalUnits l u hu,
      sourceQlEmbeddingUnitMap_frobenius l place u⟩

/-- The target Frobenius is exactly the l.value-power map on the exact image. -/
theorem sourceQlEmbeddingIntegralUnitImage_frobenius_eq
    (v : sourceQlEmbeddingIntegralUnitImage l place) :
    (targetQlIntegralUnitFrobenius place v :
      (Integers (CommonPrimeCompletion place))ˣ) = v ^ l.value := rfl

/-- Exact residual: the image is Frobenius-stable, but equality with all target
integral units remains the surjectivity statement from
SourceQlEmbeddingIntegralUnits. -/
theorem sourceQlEmbeddingIntegralUnitImage_frobenius_residual :
    sourceQlEmbeddingIntegralUnitImage l place =
        (sourceQlEmbeddingUnitMap l place).range
      ∧
    (sourceQlEmbeddingIntegralUnitImage l place = ⊤ ↔
      Function.Surjective (sourceQlEmbeddingUnitMap l place)) :=
  sourceQlEmbeddingIntegralUnitImage_exactResidual l place

/-- The unit embedding commutes with the iterated (l.value)^n-power map. -/
theorem sourceQlEmbeddingUnitMap_lPower_iterate
    (u : (Integers (sourceLocalField l))ˣ) (n : ℕ) :
    sourceQlEmbeddingUnitMap l place (u ^ (l.value ^ n)) =
      (sourceQlEmbeddingUnitMap l place u) ^ (l.value ^ n) :=
  map_pow (sourceQlEmbeddingUnitMap l place) u (l.value ^ n)

/-- The exact integral-unit image is stable under all iterates of the target
Frobenius. -/
theorem sourceQlEmbeddingIntegralUnitImage_frobenius_iterate_mem
    (n : ℕ) (v : sourceQlEmbeddingIntegralUnitImage l place) :
    (targetQlIntegralUnitFrobenius place^[n]) v ∈
      sourceQlEmbeddingIntegralUnitImage l place := by
  induction n with
  | zero => simpa using v.property
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact sourceQlEmbeddingIntegralUnitImage_frobenius_mem l place ih

/-- The principal-unit image is stable under all iterates of the target
Frobenius. -/
theorem sourceQlEmbeddingPrincipalUnitImage_frobenius_iterate_mem
    (n : ℕ) (v : sourceQlEmbeddingPrincipalUnitImage l place) :
    (targetQlIntegralUnitFrobenius place^[n]) v ∈
      sourceQlEmbeddingPrincipalUnitImage l place := by
  induction n with
  | zero => simpa using v.property
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact sourceQlEmbeddingPrincipalUnitImage_frobenius_mem l place ih

/-- The unit-level l.value-power Frobenius image of a source principal unit is
the embedded principal power. -/
theorem sourceQlEmbeddingUnitMap_principalUnit_frobenius
    (u : principalUnits (K := sourceLocalField l)) :
    sourceQlEmbeddingUnitMap l place
        ((u : (Integers (sourceLocalField l))ˣ) ^ l.value) =
      (sourceQlEmbeddingUnitMap l place
        (u : (Integers (sourceLocalField l))ˣ)) ^ l.value :=
  sourceQlEmbeddingUnitMap_frobenius l place _

/-! The image is Frobenius-stable and the embedding is injective, but no
surjectivity onto all target integral units is asserted.  The exact equality
condition is the surjectivity statement recorded above. -/


end

end ABCBridge.SourceQlEmbeddingUnitFrobenius
