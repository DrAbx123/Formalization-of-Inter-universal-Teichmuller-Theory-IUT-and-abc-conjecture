import tmp.sheaf.n8.closure.EtaCharFormulaInstantiation
import tmp.sheaf.n8.closure.EtaOrbitNonnegativeBounded
import tmp.sheaf.n8.closure.EtaTensorAutomorphismInterfaceActual

/-!
# EtaNNOrbitHullBoundActual

Actual q-volume of the finite nonnegative orbit lattice `g^k * O` in `Kf`,
using the actual general-q Haar scaling formula.  The `ℕ`-orbit hull in the
tensor block has no available Haar measure; that interface gap is recorded.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaNNOrbitHullBoundActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaCharFormulaInstantiation
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open LeanFormal.IUT.N8Closure.EtaOrbitNonnegativeBounded
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismInterfaceActual
open LeanFormal.IUT.N8Closure.FiniteObservationHull
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open MeasureTheory
open scoped NNReal ENNReal Pointwise NormedField TensorProduct

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X
abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)
abbrev g0 : Kf X := gNonIntegral X

theorem g0_ne_zero : g0 X ≠ 0 := gNonIntegral_ne_zero X

/-- Actual q-volume of the finite nonnegative orbit lattice `g^k * O`. -/
theorem qORegion_gpow_measure (g : Kf X) (hg : g ≠ 0) (k : ℕ) :
    (Measure.addHaar : Measure (Kf X)) (qORegion X (g ^ k)) =
      ENNReal.ofReal ((‖g‖ ^ k) ^
        (Module.finrank ℚ_[nativePrime X] (Kf X))) *
        (Measure.addHaar : Measure (Kf X)) (Integers (Kf X) : Set (Kf X)) := by
  have hpow : g ^ k ≠ 0 := pow_ne_zero k hg
  have htarget := (generalQHaarScalingTarget_actual X) (Units.mk0 (g ^ k) hpow)
  simpa [Units.val_mk0, norm_pow, pow_mul] using htarget

/-- Exact finite-orbit volume expression with the exponent `k * d`. -/
theorem qORegion_gpow_measure' (g : Kf X) (hg : g ≠ 0) (k : ℕ) :
    (Measure.addHaar : Measure (Kf X)) (qORegion X (g ^ k)) =
      ENNReal.ofReal ((‖g‖) ^ (k *
        Module.finrank ℚ_[nativePrime X] (Kf X))) *
        (Measure.addHaar : Measure (Kf X)) (Integers (Kf X) : Set (Kf X)) := by
  rw [qORegion_gpow_measure X g hg k, ← pow_mul]

/-- Exact gap: the `ℕ`-orbit tensor hull `nnOrbitSub` has no additive Haar
measure / finite-volume interface currently; only the `Kf`-side lattices
`g^k * O` have an actual q-volume. -/
def MissingNNTensorHullMeasure (X : N8NativeInput l) : Prop :=
  Nonempty (MeasurableSpace (E X))

end LeanFormal.IUT.N8Closure.EtaNNOrbitHullBoundActual