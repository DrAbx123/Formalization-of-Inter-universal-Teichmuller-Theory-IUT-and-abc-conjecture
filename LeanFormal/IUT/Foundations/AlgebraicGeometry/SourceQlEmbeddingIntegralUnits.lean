import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlEmbeddingConsumer
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-!
# Integral units of the actual Q_l -> F_v embedding

This file studies the actual monoid map

  (Integers Q_l)^x  ->  (Integers F_v)^x

induced by the isometric algebra-map embedding.  It proves the exact image
subgroup, injectivity, norm behaviour, the principal-unit intersection, and the
exact l.value/p-power compatibility.  Equality with all target integral units is
equivalent to surjectivity; the residual is stated explicitly.

No theta spec or alias is used.
-/

namespace ABCBridge.SourceQlEmbeddingIntegralUnits

noncomputable section

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open ABCBridge.SourceQlEmbeddingConsumer
open scoped NumberField

variable {F : Type} [Field F] [NumberField F]
variable (l : LeanFormal.IUT.PrimeGeFive)
variable (place : FinitePlaceAtPrime F l.value)

local instance sourceQlIntegralUnitsPrimeFact : Fact (Nat.Prime l.value) :=
  l.factPrime

/-! ## 1. The exact integral-unit image -/

/-- Exact image of the source integral units under the actual embedding. -/
noncomputable def sourceQlEmbeddingIntegralUnitImage :
    Subgroup (Integers (CommonPrimeCompletion place))ˣ :=
  (sourceQlEmbeddingUnitMap l place).range

/-- Membership in the integral-unit image. -/
theorem sourceQlEmbeddingIntegralUnitImage_mem_iff
    (v : (Integers (CommonPrimeCompletion place))ˣ) :
    v ∈ sourceQlEmbeddingIntegralUnitImage l place ↔
      ∃ u : (Integers (sourceLocalField l))ˣ,
        sourceQlEmbeddingUnitMap l place u = v :=
  MonoidHom.mem_range

/-- Every image element has a source integral-unit preimage. -/
theorem sourceQlEmbeddingIntegralUnitImage_exists_preimage
    (v : sourceQlEmbeddingIntegralUnitImage l place) :
    ∃ u : (Integers (sourceLocalField l))ˣ,
      sourceQlEmbeddingUnitMap l place u = v :=
  (sourceQlEmbeddingIntegralUnitImage_mem_iff l place v).mp v.property

/-- The image as a set of target integral units. -/
theorem sourceQlEmbeddingIntegralUnitImage_coe :
    (sourceQlEmbeddingIntegralUnitImage l place :
      Set (Integers (CommonPrimeCompletion place))ˣ) =
      Set.range (sourceQlEmbeddingUnitMap l place) := rfl

/-- The actual unit map is injective, direct form. -/
theorem sourceQlEmbeddingIntegralUnitMap_injective :
    Function.Injective (sourceQlEmbeddingUnitMap l place) := by
  intro u v h
  apply Units.ext
  apply Subtype.ext
  have hval := congrArg (fun w : (Integers (CommonPrimeCompletion place))ˣ =>
    (w.val : CommonPrimeCompletion place)) h
  rw [sourceQlEmbeddingUnitMap_val l place u,
    sourceQlEmbeddingUnitMap_val l place v] at hval
  exact sourceQlEmbedding_injective l place hval

/-- The range description of the integral-unit image. -/
theorem sourceQlEmbeddingIntegralUnitImage_eq_range :
    sourceQlEmbeddingIntegralUnitImage l place =
      (sourceQlEmbeddingUnitMap l place).range := rfl

/-! ## 2. Norm and valuation behaviour -/

/-- The target norm of a transported integral unit equals the source norm. -/
theorem sourceQlEmbeddingUnitMap_norm_eq
    (u : (Integers (sourceLocalField l))ˣ) :
    ‖((sourceQlEmbeddingUnitMap l place u).val :
      CommonPrimeCompletion place)‖ = ‖(u.val : sourceLocalField l)‖ := by
  rw [sourceQlEmbeddingUnitMap_val]
  exact sourceQlEmbedding_norm l place _

/-- Transported integral units are norm-one units. -/
theorem sourceQlEmbeddingUnitMap_norm_one
    (u : (Integers (sourceLocalField l))ˣ) :
    ‖((sourceQlEmbeddingUnitMap l place u).val :
      CommonPrimeCompletion place)‖ = 1 := by
  rw [sourceQlEmbeddingUnitMap_norm_eq, norm_unit_eq_one]

/-- The source integral unit itself has norm one. -/
theorem sourceQlIntegralUnit_norm_one
    (u : (Integers (sourceLocalField l))ˣ) :
    ‖(u.val : sourceLocalField l)‖ = 1 :=
  norm_unit_eq_one u

/-- The transported unit lies in the target valuation integers because it is a
target integral unit; its norm is exactly one. -/
theorem sourceQlEmbeddingUnitMap_mem_integers
    (u : (Integers (sourceLocalField l))ˣ) :
    ((sourceQlEmbeddingUnitMap l place u).val :
      CommonPrimeCompletion place) ∈
      Integers (CommonPrimeCompletion place) :=
  (sourceQlEmbeddingUnitMap l place u).val.property

/-! ## 3. Principal-unit intersection -/

/-- Image of the source principal units under the actual unit map. -/
noncomputable def sourceQlEmbeddingPrincipalUnitImage :
    Subgroup (Integers (CommonPrimeCompletion place))ˣ :=
  Subgroup.map (sourceQlEmbeddingUnitMap l place)
    (principalUnits (K := sourceLocalField l))

/-- Membership in the principal-unit image. -/
theorem sourceQlEmbeddingPrincipalUnitImage_mem_iff
    (v : (Integers (CommonPrimeCompletion place))ˣ) :
    v ∈ sourceQlEmbeddingPrincipalUnitImage l place ↔
      ∃ u : (Integers (sourceLocalField l))ˣ,
        u ∈ principalUnits ∧ sourceQlEmbeddingUnitMap l place u = v :=
  Subgroup.mem_map

/-- A source unit is principal if and only if its transport is principal. -/
theorem sourceQlEmbeddingUnitMap_mem_principalUnits_iff
    (u : (Integers (sourceLocalField l))ˣ) :
    u ∈ principalUnits ↔
      sourceQlEmbeddingUnitMap l place u ∈ principalUnits := by
  constructor
  · exact sourceQlEmbeddingUnitMap_mem_principalUnits l place u
  · intro hu
    rw [mem_principalUnits_iff] at hu ⊢
    have hnorm := sourceQlEmbedding_norm l place
      ((u.val : sourceLocalField l) - 1)
    rw [sourceQlEmbeddingUnitMap_val, map_sub, map_one] at hu
    simpa only [map_sub, map_one, sourceQlEmbeddingUnitMap_val,
      sourceQlEmbeddingUnitMap] using hu

/-- The source principal-unit image is exactly the intersection of the full
integral-unit image with the target principal units. -/
theorem sourceQlEmbeddingIntegralUnitImage_inf_principalUnits :
    sourceQlEmbeddingIntegralUnitImage l place ⊓
        principalUnits (K := CommonPrimeCompletion place) =
      sourceQlEmbeddingPrincipalUnitImage l place := by
  apply le_antisymm
  · intro v hv
    rw [Subgroup.mem_inf] at hv
    obtain ⟨u, rfl⟩ :=
      (sourceQlEmbeddingIntegralUnitImage_mem_iff l place v).mp hv.1
    exact (Subgroup.mem_map).mpr
      ⟨u, (sourceQlEmbeddingUnitMap_mem_principalUnits_iff l place u).mpr hv.2, rfl⟩
  · intro v hv
    obtain ⟨u, hu, rfl⟩ :=
      (sourceQlEmbeddingPrincipalUnitImage_mem_iff l place v).mp hv
    exact Subgroup.mem_inf.mpr
      ⟨(sourceQlEmbeddingIntegralUnitImage_mem_iff l place
          (sourceQlEmbeddingUnitMap l place u)).mpr ⟨u, rfl⟩,
        sourceQlEmbeddingUnitMap_mem_principalUnits l place u hu⟩

/-! ## 4. Exact l.value/p-power compatibility -/

/-- The unit transport commutes with the actual p-power Frobenius power. -/
theorem sourceQlEmbeddingUnitMap_power
    (u : (Integers (sourceLocalField l))ˣ) (n : ℕ) :
    sourceQlEmbeddingUnitMap l place (u ^ n) =
      (sourceQlEmbeddingUnitMap l place u) ^ n :=
  map_pow (sourceQlEmbeddingUnitMap l place) u n

/-- In particular the l.value-th power is transported to the l.value-th power. -/
theorem sourceQlEmbeddingUnitMap_lPower
    (u : (Integers (sourceLocalField l))ˣ) :
    sourceQlEmbeddingUnitMap l place (u ^ l.value) =
      (sourceQlEmbeddingUnitMap l place u) ^ l.value :=
  sourceQlEmbeddingUnitMap_power l place u l.value

/-- Iterated l.value-power compatibility. -/
theorem sourceQlEmbeddingUnitMap_lPower_iterate
    (u : (Integers (sourceLocalField l))ˣ) (n : ℕ) :
    sourceQlEmbeddingUnitMap l place (u ^ (l.value ^ n)) =
      (sourceQlEmbeddingUnitMap l place u) ^ (l.value ^ n) :=
  sourceQlEmbeddingUnitMap_power l place u (l.value ^ n)

/-! ## 5. Equality and exact residual -/

/-- The integral-unit image equals all target integral units exactly when the
actual unit map is surjective. -/
theorem sourceQlEmbeddingIntegralUnitImage_eq_top_iff_surjective :
    sourceQlEmbeddingIntegralUnitImage l place = ⊤ ↔
      Function.Surjective (sourceQlEmbeddingUnitMap l place) :=
  MonoidHom.range_eq_top

/-- Surjectivity gives equality with all target integral units. -/
theorem sourceQlEmbeddingIntegralUnitImage_eq_top_of_surjective
    (h : Function.Surjective (sourceQlEmbeddingUnitMap l place)) :
    sourceQlEmbeddingIntegralUnitImage l place = ⊤ :=
  (sourceQlEmbeddingIntegralUnitImage_eq_top_iff_surjective l place).mpr h

/-- Non-surjectivity gives strict containment. -/
theorem sourceQlEmbeddingIntegralUnitImage_ne_top_of_not_surjective
    (h : ¬ Function.Surjective (sourceQlEmbeddingUnitMap l place)) :
    sourceQlEmbeddingIntegralUnitImage l place ≠ ⊤ := by
  intro heq
  exact h ((sourceQlEmbeddingIntegralUnitImage_eq_top_iff_surjective l place).mp heq)

/-- Exact residual: the image is the actual Q_l integral-unit subgroup; equality
with all target integral units is conditional on surjectivity. -/
theorem sourceQlEmbeddingIntegralUnitImage_exactResidual :
    sourceQlEmbeddingIntegralUnitImage l place =
        (sourceQlEmbeddingUnitMap l place).range
      ∧
    (sourceQlEmbeddingIntegralUnitImage l place = ⊤ ↔
      Function.Surjective (sourceQlEmbeddingUnitMap l place)) :=
  ⟨rfl, sourceQlEmbeddingIntegralUnitImage_eq_top_iff_surjective l place⟩

end

end ABCBridge.SourceQlEmbeddingIntegralUnits
