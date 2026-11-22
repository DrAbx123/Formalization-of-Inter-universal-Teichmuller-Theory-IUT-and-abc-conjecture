import tmp.sheaf.n8.closure.EtaUniformizerRelationActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellLattice
import Mathlib.Topology.Algebra.Valued.LocallyCompact

/-!
# EtaDVRInstanceActual

Actual compactness of `Integers (Kf X)`, and the conditional DVR instance via
Mathlib's `Valued.integer.isDiscreteValuationRing_of_compactSpace`.

Exact missing production step: the valuation-nontriviality instance
`(Valued.v (R := Kf X)).IsNontrivial` (equivalently the normalized/nontrivial
normed-field structure needed to compare `fPlaceP_norm` with the valuation).
Without it the compactness-to-DVR theorem cannot be discharged.  No arbitrary
instance is added.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaDVRInstanceActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField

variable {l : PrimeGeFive} (X : N8NativeInput l)

local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

noncomputable instance integersCompactSpace : CompactSpace (Integers (Kf X)) := by
  exact isCompact_iff_compactSpace.mp
    (isCompact_valuationIntegerLattice (K := Kf X) (p := nativePrime X))

def ValuationNontrivialAtKf (X : N8NativeInput l) : Prop :=
  (Valued.v (R := Kf X)).IsNontrivial

noncomputable def integersDVR_of_valuationNontrivial
    (h : ValuationNontrivialAtKf X) : IsDiscreteValuationRing (Integers (Kf X)) := by
  letI : (Valued.v (R := Kf X)).IsNontrivial := h
  haveI hc : CompactSpace (Valued.integer (Kf X)) := by
    change CompactSpace (Integers (Kf X))
    exact integersCompactSpace X
  exact Valued.integer.isDiscreteValuationRing_of_compactSpace

end LeanFormal.IUT.N8Closure.EtaDVRInstanceActual