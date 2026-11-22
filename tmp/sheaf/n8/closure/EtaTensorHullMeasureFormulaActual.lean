import tmp.sheaf.n8.closure.EtaTensorHullMeasureActual
import tmp.sheaf.n8.closure.EtaDVRInstanceActual

/-!
# EtaTensorHullMeasureFormulaActual

Measurability of `qORegion` (compact image) and the exact remaining measure
transport step.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaTensorHullMeasureFormulaActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaTensorHullMeasureActual
open LeanFormal.IUT.N8Closure.EtaTensorNaturalityActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismActual3
open LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaDVRInstanceActual
open LeanFormal.IUT.N8Closure.EtaNNOrbitHullBoundActual
open LeanFormal.IUT.N8Closure.EtaOrbitNonnegativeBounded
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open MeasureTheory
open scoped NNReal ENNReal Pointwise NormedField TensorProduct

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X
abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)

theorem measurableSet_qORegion (q : Kf X) :
    MeasurableSet (qORegion X q) := by
  rw [qORegion]
  apply IsCompact.measurableSet
  have hcont : Continuous (fun o : Integers (Kf X) => q * (o : Kf X)) :=
    continuous_const.mul continuous_subtype_val
  have hK : IsCompact (Set.univ : Set (Integers (Kf X))) := isCompact_univ
  exact hK.image hcont

/-- Exact missing: the lattice image identity and map/preimage measure step. -/
def MissingNnLatticeMeasureTransport (X : N8NativeInput l) : Prop :=
  (∀ (g : Kf X) (k : ℕ), nnLattice X g k = (tau X).symm '' qORegion X (g ^ k)) ∧
  (∀ (g : Kf X) (hg : g ≠ 0) (k : ℕ),
    tensorHaar X (nnLattice X g k) =

      ENNReal.ofReal ((‖g‖ ^ k) ^

        (Module.finrank ℚ_[nativePrime X] (Kf X))) *

        (Measure.addHaar : Measure (Kf X)) (Integers (Kf X) : Set (Kf X)))

end LeanFormal.IUT.N8Closure.EtaTensorHullMeasureFormulaActual