import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceLogKummerIdentification
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmFunctoriality
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitGaloisDescent
import LeanFormal.IUT.Foundations.LocalFields.LogarithmSeriesTransport
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-!
# Actual Q_l embedding consumer

This file proves the actual consumer interface for the isometric embedding

  sourceLocalField l = Q_l  ->  CommonPrimeCompletion place = F_v

at a place whose rational prime is l.value.  It provides:

1. the ring embedding and its isometry/injectivity;
2. the induced map on all integral units;
3. the induced map on principal units;
4. compatibility of the actual principal-unit logarithms;
5. the induced additive embedding of the unscaled source log-shell into the
   target principal-unit log image;
6. the exact p/l scaling square: source l.value-scaling is carried to target
   p-scaling at p = l.value.

No theta-link data is used or assumed, and no theta spec is inhabited or
aliased here.  The embedding is not an identification of F_v with Q_l.
-/

namespace ABCBridge.SourceQlEmbeddingConsumer

noncomputable section

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NumberField

variable {F : Type} [Field F] [NumberField F]
variable (l : LeanFormal.IUT.PrimeGeFive)
variable (place : FinitePlaceAtPrime F l.value)

local instance sourceQlEmbeddingConsumerPrimeFact : Fact (Nat.Prime l.value) :=
  l.factPrime

/-! ## 1. The actual ring embedding -/

/-- The actual embedding Q_l -> F_v is the algebra map. -/
noncomputable def sourceQlEmbeddingRingHom :
    sourceLocalField l →+* CommonPrimeCompletion place :=
  algebraMap (sourceLocalField l) (CommonPrimeCompletion place)

/-- The actual source Q_l embedding is an isometry. -/
theorem sourceQlEmbedding_isometry :
    Isometry (sourceQlEmbeddingRingHom l place) :=
  isometry_localField_algebraMap (K := sourceLocalField l)
    (L := CommonPrimeCompletion place)

/-- The actual source Q_l embedding is injective. -/
theorem sourceQlEmbedding_injective :
    Function.Injective (sourceQlEmbeddingRingHom l place) :=
  (sourceQlEmbedding_isometry l place).injective

/-- The actual source Q_l embedding preserves norms. -/
theorem sourceQlEmbedding_norm (x : sourceLocalField l) :
    ‖sourceQlEmbeddingRingHom l place x‖ = ‖x‖ :=
  norm_map_of_isometry (sourceQlEmbeddingRingHom l place)
    (sourceQlEmbedding_isometry l place) x

/-- The embedding sends the source Q_l to the target completion. -/
theorem sourceQlEmbedding_apply (x : sourceLocalField l) :
    sourceQlEmbeddingRingHom l place x =
      algebraMap (sourceLocalField l) (CommonPrimeCompletion place) x :=
  rfl

/-! ## 2. Integral-unit transport -/

/-- The actual transport of all source integral units. -/
noncomputable def sourceQlEmbeddingUnitMap :
    (Integers (sourceLocalField l))ˣ →*
      (Integers (CommonPrimeCompletion place))ˣ :=
  integralUnitMap (sourceQlEmbeddingRingHom l place)
    (sourceQlEmbedding_isometry l place)

/-- The transported unit has the expected value. -/
theorem sourceQlEmbeddingUnitMap_val
    (u : (Integers (sourceLocalField l))ˣ) :
    ((sourceQlEmbeddingUnitMap l place u).val :
      CommonPrimeCompletion place) =
      sourceQlEmbeddingRingHom l place (u.val : sourceLocalField l) :=
  integralUnitMap_val (sourceQlEmbeddingRingHom l place)
    (sourceQlEmbedding_isometry l place) u

/-- The unit transport is multiplicative. -/
theorem sourceQlEmbeddingUnitMap_mul
    (u v : (Integers (sourceLocalField l))ˣ) :
    sourceQlEmbeddingUnitMap l place (u * v) =
      sourceQlEmbeddingUnitMap l place u *
        sourceQlEmbeddingUnitMap l place v :=
  map_mul (sourceQlEmbeddingUnitMap l place) u v

/-- The unit transport preserves powers. -/
theorem sourceQlEmbeddingUnitMap_pow
    (u : (Integers (sourceLocalField l))ˣ) (n : ℕ) :
    sourceQlEmbeddingUnitMap l place (u ^ n) =
      (sourceQlEmbeddingUnitMap l place u) ^ n :=
  map_pow (sourceQlEmbeddingUnitMap l place) u n

/-! ## 3. Principal-unit transport -/

/-- The unit transport carries principal units to principal units. -/
theorem sourceQlEmbeddingUnitMap_mem_principalUnits
    (u : (Integers (sourceLocalField l))ˣ) (hu : u ∈ principalUnits) :
    sourceQlEmbeddingUnitMap l place u ∈ principalUnits :=
  integralUnitMap_mem_principalUnits (sourceQlEmbeddingRingHom l place)
    (sourceQlEmbedding_isometry l place) u hu

/-- The actual principal-unit log is compatible with the embedding. -/
theorem sourceQlEmbedding_principalUnitLog_compat
    (u : principalUnits (K := sourceLocalField l)) :
    sourceQlEmbeddingRingHom l place
        (principalUnitLog (K := sourceLocalField l) u) =
      principalUnitLog (K := CommonPrimeCompletion place)
        ⟨sourceQlEmbeddingUnitMap l place
            (u : (Integers (sourceLocalField l))ˣ),
          sourceQlEmbeddingUnitMap_mem_principalUnits l place
            (u : (Integers (sourceLocalField l))ˣ) u.property⟩ := by
  change sourceQlEmbeddingRingHom l place
      (log1p (((u : (Integers (sourceLocalField l))ˣ).val :
        sourceLocalField l) - 1)) =
    log1p (((sourceQlEmbeddingUnitMap l place
      (u : (Integers (sourceLocalField l))ˣ)).val :
        CommonPrimeCompletion place) - 1)
  have hval : ((sourceQlEmbeddingUnitMap l place
      (u : (Integers (sourceLocalField l))ˣ)).val :
        CommonPrimeCompletion place) =
      sourceQlEmbeddingRingHom l place
        (((u : (Integers (sourceLocalField l))ˣ).val : sourceLocalField l)) :=
    integralUnitMap_val (sourceQlEmbeddingRingHom l place)
      (sourceQlEmbedding_isometry l place)
      (u : (Integers (sourceLocalField l))ˣ)
  rw [hval, ← map_one, ← map_sub]
  exact log1p_map (p := l.value) (K := sourceLocalField l)
    (L := CommonPrimeCompletion place)
    (e := sourceQlEmbeddingRingHom l place)
    (he := sourceQlEmbedding_isometry l place)
    (((u : (Integers (sourceLocalField l))ˣ).val : sourceLocalField l) - 1)
    ((mem_principalUnits_iff _).mp u.property)

/-! ## 4. Log-shell embedding -/

/-- The induced additive map on the unscaled source Q_l log-shell. -/
noncomputable def sourceQlEmbeddingLogShellMap :
    sourceLogShell l →+
      principalUnitLogImage (K := CommonPrimeCompletion place) l.value where
  toFun x :=
    ⟨sourceQlEmbeddingRingHom l place (x : sourceLocalField l), by
      rcases x.property with ⟨u, hu⟩
      refine ⟨⟨sourceQlEmbeddingUnitMap l place
          (u : (Integers (sourceLocalField l))ˣ),
        sourceQlEmbeddingUnitMap_mem_principalUnits l place
          (u : (Integers (sourceLocalField l))ˣ) u.property⟩, ?_⟩
      rw [← hu]
      simpa only using
        (sourceQlEmbedding_principalUnitLog_compat l place u).symm⟩
  map_zero' := by
    ext
    rw [sourceQlEmbeddingRingHom, map_zero]
    rfl
  map_add' x y := by
    ext
    rw [sourceQlEmbeddingRingHom, map_add]
    rfl

/-- The log-shell embedding is the ring embedding on coordinates. -/
@[simp] theorem sourceQlEmbeddingLogShellMap_coe (x : sourceLogShell l) :
    (sourceQlEmbeddingLogShellMap l place x :
      CommonPrimeCompletion place) =
      sourceQlEmbeddingRingHom l place (x : sourceLocalField l) :=
  rfl

/-- The log-shell embedding is injective. -/
theorem sourceQlEmbeddingLogShellMap_injective :
    Function.Injective (sourceQlEmbeddingLogShellMap l place) := by
  intro x y h
  apply Subtype.ext
  exact sourceQlEmbedding_injective l place (congrArg Subtype.val h)

/-! ## 5. Target p-scaling and the exact p/l square -/

/-- The actual p-fold scaling on the target principal-unit log image, at
p = l.value. -/
noncomputable def sourceQlEmbeddingTargetPScaling :
    principalUnitLogImage (K := CommonPrimeCompletion place) l.value →+
      principalUnitLogImage (K := CommonPrimeCompletion place) l.value where
  toFun x :=
    ⟨(l.value : CommonPrimeCompletion place) *
        (x : CommonPrimeCompletion place), by
      rcases x.property with ⟨u, hu⟩
      refine ⟨u ^ l.value, ?_⟩
      rw [← hu]
      exact principalUnitLog_pow (K := CommonPrimeCompletion place)
        l.value l.value u⟩
  map_zero' := by
    ext
    simp
  map_add' x y := by
    ext
    simp [mul_add]

@[simp] theorem sourceQlEmbeddingTargetPScaling_apply
    (x : principalUnitLogImage (K := CommonPrimeCompletion place) l.value) :
    (sourceQlEmbeddingTargetPScaling l place x :
      CommonPrimeCompletion place) =
      (l.value : CommonPrimeCompletion place) *
        (x : CommonPrimeCompletion place) :=
  rfl

/-- The source l.value-scaling on the unscaled Q_l log-shell is carried to the
target p-scaling at p = l.value.  This is the exact p/l scaling square. -/
theorem sourceQlEmbedding_scalingSquare (x : sourceLogShell l) :
    sourceQlEmbeddingLogShellMap l place (sourcePScaling l x) =
      sourceQlEmbeddingTargetPScaling l place
        (sourceQlEmbeddingLogShellMap l place x) := by
  apply Subtype.ext
  change sourceQlEmbeddingRingHom l place
      ((l.value : sourceLocalField l) * (x : sourceLocalField l)) =
    (l.value : CommonPrimeCompletion place) *
      (sourceQlEmbeddingRingHom l place (x : sourceLocalField l))
  rw [map_mul, map_natCast]

/-- The target scaling is exactly multiplication by the source prime l.value. -/
theorem sourceQlEmbeddingTargetPScaling_eq_mul
    (x : principalUnitLogImage (K := CommonPrimeCompletion place) l.value) :
    (sourceQlEmbeddingTargetPScaling l place x :
      CommonPrimeCompletion place) =
      (l.value : CommonPrimeCompletion place) *
        (x : CommonPrimeCompletion place) :=
  rfl

/-- The source scaling is exactly multiplication by l.value on the unscaled
source Q_l log-shell. -/
theorem sourceQlEmbeddingSourcePScaling_eq_mul (x : sourceLogShell l) :
    (sourcePScaling l x : sourceLocalField l) =
      (l.value : sourceLocalField l) * (x : sourceLocalField l) :=
  rfl

/-- Exact prime exposure for the actual place: the rational prime below the
normalized completion is l.value. -/
theorem sourceQlEmbedding_primeExposure :
    (completionRationalPrime (K := F) place.val).val = l.value :=
  place.property

/-- The log-shell embedding commutes with the source power law after target
p-scaling, in the exact p/l form. -/
theorem sourceQlEmbedding_scalingSquare_iterate
    (n : ℕ) (x : sourceLogShell l) :
    sourceQlEmbeddingLogShellMap l place
        ((sourcePScaling l)^[n] x) =
      (sourceQlEmbeddingTargetPScaling l place)^[n]
        (sourceQlEmbeddingLogShellMap l place x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      change sourceQlEmbeddingLogShellMap l place
          ((sourcePScaling l)^[n] (sourcePScaling l x)) =
        (sourceQlEmbeddingTargetPScaling l place)^[n]
          (sourceQlEmbeddingTargetPScaling l place
            (sourceQlEmbeddingLogShellMap l place x))
      rw [ih (sourcePScaling l x)]
      exact congrArg ((sourceQlEmbeddingTargetPScaling l place)^[n])
        (sourceQlEmbedding_scalingSquare l place x)

end

end ABCBridge.SourceQlEmbeddingConsumer
