import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlUnitTransport
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-!
# Q_l source theta-link bridge audit

This file records the actual source objects that exist and separates them from
the theta-link data that does NOT exist in the tree.  It contains no source
card, no placeholder structure, and no unconditional theta-link assertion.

## Actual objects (available, referenced in Lean below)

* source field: sourceLocalField l = Q_l;
* source principal units: sourcePrincipalUnits l = principalUnits (K := Q_l);
* source log-Kummer map: sourceLogKummer l = principalUnitLog (K := Q_l);
* source log-shell: sourceLogShell l = principalUnitLogImage (K := Q_l) l.value,
  the UNSCALED principal-unit log image;
* source Frobenius: sourceFrobenius l u = u ^ l.value;
* source scaling: sourcePScaling l x = l.value * x on sourceLogShell l;
* actual embedding into a normalized completion: sourceQlToTargetRingHom l place
  and its log-shell map sourceQlLogShellMap l place from SourceQlCarrierMap;
* consumer p-scaling: consumerLogShellFrobenius place at p = l.value.

## Exact missing objects for an actual theta-link bridge (none constructed)

1. The actual source theta object A_Theta, its cover/projection and base change,
   and the source theta divisor/unit comparison Mq -> M_Theta.  No such object
   is defined in this tree.
2. A comparison of the source Q_l unit/log-shell carrier with the complete
   normalized completion F_v that is more than the algebra-map subgroup
   embedding: the embedding source -> F_v is not an identification of F_v with
   Q_l.  The theta-link comparison would have to supply the object-level data
   identifying the source theta side, not just the scalar embedding.
3. Root/deck compatibility: mu_(2l), the l-Z/deck ambiguity and conjugate
   synchronization between the source theta and the normalized completion.
4. Only after (1)-(3) may one identify the source l.value-scaling with the
   consumer p-scaling as the SAME theta-link operation.  The actual commuting
   square below proves only that the embedding carries source scaling into
   consumer p-scaling; it is not the theta-link identification.

The residual is therefore a source-data gap, not a missing scalar identity.
-/

namespace ABCBridge.SourceQlThetaLinkBridge

noncomputable section

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open ABCBridge.SourceQlCarrierMap
open ABCBridge.SourceQlUnitTransport
open ABCBridge.LogShellFrobeniusConsumerGeneral
open scoped NumberField

variable {F : Type} [Field F] [NumberField F]
variable (l : LeanFormal.IUT.PrimeGeFive)
variable (place : FinitePlaceAtPrime F l.value)

local instance sourceQlThetaPrimeFact : Fact (Nat.Prime l.value) :=
  l.factPrime

/-- Actual source local-field carrier. -/
theorem actualSourceLocalField :
    sourceLocalField l = ℚ_[l.value] := rfl

/-- Actual source log-shell is the unscaled Q_l principal-unit log image. -/
theorem actualSourceLogShell :
    (sourceLogShell l : Set (sourceLocalField l)) =
      Set.range (fun u : principalUnits (K := sourceLocalField l) =>
        sourceLogKummer l u) := rfl

/-- Actual source scaling is l.value-fold scaling on the unscaled image. -/
theorem actualSourceScaling (x : sourceLogShell l) :
    (sourcePScaling l x : sourceLocalField l) =
      (l.value : sourceLocalField l) * (x : sourceLocalField l) := rfl

/-- Actual source embedding into the normalized completion is isometric. -/
theorem actualSourceEmbeddingIsometry :
    Isometry (sourceQlToTargetRingHom l place) :=
  sourceQlToTargetRingHom_isometry l place

/-- Actual commuting square: the embedding carries source l.value-scaling to
consumer p-scaling at p = l.value.  This is NOT the theta-link identification. -/
theorem actualEmbeddingScalingSquare (x : sourceLogShell l) :
    sourceQlLogShellMap l place (sourcePScaling l x) =
      consumerLogShellFrobenius place (sourceQlLogShellMap l place x) :=
  sourceQlLogShellMap_pScaling l place x

/-- Actual consumer interface at p = l.value. -/
theorem actualConsumerScalingExposed (n : ℕ) (x : ConsumerLogShell place) :
    (((consumerLogShellFrobenius place)^[n]) x : ConsumerField place) =
      (l.value : ConsumerField place) ^ n * (x : ConsumerField place) := by
  exact consumerLogShellFrobenius_iterate_apply place x n

/-- Exact theta-link residual object list, as a Lean value for documentation
and consumer bookkeeping.  This is not a source card and proves nothing. -/
def sourceThetaLinkResiduals : List String :=
  [ "source theta object A_Theta and projection/base change",
    "source theta divisor and unit comparison Mq -> M_Theta",
    "mu_(2l)/l-Z deck and root compatibility",
    "conjugate synchronization between source theta and normalized completion",
    "object-level identification (not only the Q_l -> F_v scalar embedding)" ]

/-- The actual embedding square is only a subgroup-level comparison: it does
not identify the whole normalized completion with the source field.  This
theorem records the exact available comparison as an additive map on the
unscaled source log-shell. -/
theorem actualEmbeddingMapIsAdditive (x y : sourceLogShell l) :
    sourceQlLogShellMap l place (x + y) =
      sourceQlLogShellMap l place x + sourceQlLogShellMap l place y :=
  map_add (sourceQlLogShellMap l place) x y

/-- The actual embedding carries the zero log-shell element to zero. -/
theorem actualEmbeddingMapZero :
    sourceQlLogShellMap l place 0 = 0 :=
  map_zero (sourceQlLogShellMap l place)

/-- The residual list has exactly the five source-theta items documented above. -/
theorem sourceThetaLinkResiduals_length :
    sourceThetaLinkResiduals.length = 5 := rfl

end

end ABCBridge.SourceQlThetaLinkBridge
