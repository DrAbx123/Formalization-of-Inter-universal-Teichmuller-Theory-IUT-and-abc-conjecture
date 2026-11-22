import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlCarrierMap
import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogShellFrobeniusConsumerGeneral
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-!
# Actual Q_l unit and log-shell transport

This file packages the actual unit transport of SourceQlCarrierMap and proves
that the concrete source l.value-scaling on the unscaled Q_l log-shell is
carried to the consumer p-scaling at the chosen normalized completion, with
p = l.value.

The transport is along the actual algebra-map embedding Q_l -> F_v.  It is not
an identification of the whole completion F_v with Q_l, and it does not supply
the theta-link comparison of SourceQlThetaLinkBridge.lean.
-/

namespace ABCBridge.SourceQlUnitTransport

noncomputable section

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open ABCBridge.SourceQlCarrierMap
open ABCBridge.LogShellFrobeniusConsumerGeneral
open scoped NumberField

variable {F : Type} [Field F] [NumberField F]
variable (l : LeanFormal.IUT.PrimeGeFive)
variable (place : FinitePlaceAtPrime F l.value)

local instance sourceQlTransportPrimeFact : Fact (Nat.Prime l.value) :=
  l.factPrime

/-- Unit transport commutes with powers. -/
theorem sourceQlUnitMap_pow (u : (Integers (sourceLocalField l))ˣ) (n : ℕ) :
    sourceQlUnitMap l place (u ^ n) =
      (sourceQlUnitMap l place u) ^ n :=
  map_pow (sourceQlUnitMap l place) u n

/-- Principal-unit logarithm scaling after transport: the transported n-th
power has logarithm n times the transported logarithm. -/
theorem sourceQl_principalUnitLog_pow
    (u : principalUnits (K := sourceLocalField l)) (n : ℕ) :
    principalUnitLog (K := CommonPrimeCompletion place)
        ⟨sourceQlUnitMap l place
            ((u : (Integers (sourceLocalField l))ˣ) ^ n),
          sourceQlUnitMap_mem_principalUnits l place
            ((u : (Integers (sourceLocalField l))ˣ) ^ n)
            ((principalUnits (K := sourceLocalField l)).pow_mem u.property n)⟩ =
      (n : CommonPrimeCompletion place) *
        principalUnitLog (K := CommonPrimeCompletion place)
          ⟨sourceQlUnitMap l place (u : (Integers (sourceLocalField l))ˣ),
            sourceQlUnitMap_mem_principalUnits l place
              (u : (Integers (sourceLocalField l))ˣ) u.property⟩ := by
  rw [sourceQlUnitMap_pow]
  exact principalUnitLog_pow (K := CommonPrimeCompletion place) l.value n
    ⟨sourceQlUnitMap l place (u : (Integers (sourceLocalField l))ˣ),
      sourceQlUnitMap_mem_principalUnits l place
        (u : (Integers (sourceLocalField l))ˣ) u.property⟩

/-- The actual source l.value-scaling on the unscaled Q_l log-shell commutes
with the consumer p-scaling (p = l.value) under the actual source embedding. -/
theorem sourceQlLogShellMap_pScaling (x : sourceLogShell l) :
    sourceQlLogShellMap l place (sourcePScaling l x) =
      consumerLogShellFrobenius place (sourceQlLogShellMap l place x) := by
  apply Subtype.ext
  rw [sourceQlLogShellMap_coe, sourcePScaling_coe, map_mul, map_natCast,
    consumerLogShellFrobenius_apply, sourceQlLogShellMap_coe]

/-- On the actual log-Kummer generator, the source Frobenius square is carried
to the consumer p-scaling square. -/
theorem sourceQlLogShellMap_frobeniusSquare
    (u : sourcePrincipalUnits l) :
    sourceQlLogShellMap l place
        (sourceLogKummerShell l (sourceFrobenius l u)) =
      consumerLogShellFrobenius place
        (sourceQlLogShellMap l place (sourceLogKummerShell l u)) := by
  rw [sourceLogKummer_square l u]
  exact sourceQlLogShellMap_pScaling l place (sourceLogKummerShell l u)

/-- Exact field-prime exposure: the consumer scale at this place is the source
prime l.value. -/
theorem sourceQlConsumer_prime_exposure :
    (LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime
      (K := F) place.val).val = l.value :=
  place.property

/-- Exact paper-scale residual: for odd l.value the paper scale is l.value;
at l.value = 2 it is 4 and the consumer action remains 2-fold. -/
theorem sourceQl_logShellScale_exposure :
    logShellScale l.value = if l.value = 2 then l.value ^ 2 else l.value := by
  unfold logShellScale
  split_ifs <;> rfl

end

end ABCBridge.SourceQlUnitTransport
