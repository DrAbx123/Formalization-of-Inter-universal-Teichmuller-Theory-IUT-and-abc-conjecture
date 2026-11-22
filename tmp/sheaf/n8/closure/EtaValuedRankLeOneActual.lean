import tmp.sheaf.n8.closure.EtaDVRInstanceActual
import tmp.sheaf.n8.closure.EtaNontriviallyNormedKfActual
import Mathlib.RingTheory.Valuation.RankOne

/-!
# EtaValuedRankLeOneActual

Actual rank-le-one/rank-one instances for `Valued.v (R := Kf X)`, transported
from the norm-derived `NormedField.valuation` instance using the scoped
`NormedField.toValued` identification.  Then the DVR instance follows from
actual compactness.  No arbitrary instance.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaValuedRankLeOneActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual
open LeanFormal.IUT.N8Closure.EtaDVRInstanceActual
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal NormedField

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

/-- Actual rank-le-one instance for the normalized valuation. -/
noncomputable instance valRankLeOne :
    Valuation.RankLeOne (Valued.v (R := Kf X)) := by
  change Valuation.RankLeOne (NormedField.valuation (K := Kf X))
  infer_instance

theorem val_fPlaceP_ne_one : (Valued.v (R := Kf X)) (fPlaceP X) ≠ 1 := by
  intro h
  have hnorm : ‖fPlaceP X‖ = 1 := by
    simpa using congrArg (fun x : ℝ≥0 => (x : ℝ)) h
  exact fPlaceP_norm_ne_one (X := X) hnorm

/-- Actual rank-one instance for the normalized valuation. -/
noncomputable instance valRankOne :
    (Valued.v (R := Kf X)).RankOne :=
  Valuation.RankLeOne.rankOne_of_exists
    (v := Valued.v (R := Kf X))
    ⟨fPlaceP X, fPlaceP_ne_zero X, val_fPlaceP_ne_one X⟩

/-- Actual DVR instance, now that rank-one is available. -/
noncomputable instance integersDVR : IsDiscreteValuationRing (Integers (Kf X)) :=
  EtaDVRInstanceActual.integersDVR_of_valuationNontrivial (X := X)
    (valRankOne (X := X)).toIsNontrivial

end LeanFormal.IUT.N8Closure.EtaValuedRankLeOneActual
