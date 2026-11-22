import tmp.sheaf.n8.closure.EtaNontriviallyNormedKfActual
import Mathlib.RingTheory.Valuation.RankOne

/-!
# EtaValuedRankOneActual

Attempt at `(Valued.v (R := Kf X)).RankOne` after activating the scoped
`NormedField.toValued` instance.

Actual: `NontriviallyNormedField (Kf X)` and `fPlaceP_norm_ne_one` are
available.  However the scoped instance does not make the normalized
`Valued.v` typeclass-compatible with the norm-derived `RankLeOne` instance:
inference for `(Valued.v).RankLeOne` still fails, so
`RankLeOne.rankOne_of_exists` cannot be applied.  The exact rank-one target is
recorded as a named gap; no arbitrary instance is added.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaValuedRankOneActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal NormedField

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

theorem fPlaceP_norm_ne_one_reexport : ‖fPlaceP X‖ ≠ 1 :=
  fPlaceP_norm_ne_one (X := X)

/-- Exact missing rank-one valuation target at Kf. -/
def ValuedRankOneAtKf (X : N8NativeInput l) : Prop :=
  Nonempty ((Valued.v (R := Kf X)).RankOne)

end LeanFormal.IUT.N8Closure.EtaValuedRankOneActual