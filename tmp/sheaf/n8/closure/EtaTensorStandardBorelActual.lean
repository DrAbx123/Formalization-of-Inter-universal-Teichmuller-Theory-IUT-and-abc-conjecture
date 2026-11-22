import tmp.sheaf.n8.closure.EtaNnLatticeImageActual

/-!
# EtaTensorStandardBorelActual

Close the transported measurable-image obligation using the defining property
of `MeasurableSpace.map`: preimages of measurable sets are measurable, and
`tau.symm` is injective, so its image of `qORegion` is measurable without a
StandardBorel/CountablySeparated instance.  Then the tensor lattice measure
formula is unconditional.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaTensorStandardBorelActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaTensorHullMeasureActual
open LeanFormal.IUT.N8Closure.EtaTensorHullMeasureFormulaActual
open LeanFormal.IUT.N8Closure.EtaNnLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorNaturalityActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismActual3
open LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual
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

local instance : MeasurableSpace (E X) :=
  MeasurableSpace.map (tau X).symm (inferInstance : MeasurableSpace (Kf X))

theorem measurableSet_transported_qORegion (g : Kf X) (k : ℕ) :
    MeasurableSet ((tau X).symm '' qORegion X (g ^ k)) := by
  rw [MeasurableSpace.map_def]
  rw [Set.preimage_image_eq _ (tau X).symm.injective]
  exact measurableSet_qORegion X (g ^ k)

theorem missingTransportedMeasurableImage_actual :
    MissingTransportedMeasurableImage X := by
  intro g k
  exact measurableSet_transported_qORegion X g k

theorem tensorHaar_nnLattice_formula_actual (g : Kf X) (hg : g ≠ 0) (k : ℕ) :
    tensorHaar X (nnLattice X g k) =
      ENNReal.ofReal ((‖g‖ ^ k) ^

        (Module.finrank ℚ_[nativePrime X] (Kf X))) *

        (Measure.addHaar : Measure (Kf X)) (Integers (Kf X) : Set (Kf X)) :=
  tensorHaar_nnLattice_formula X g hg k (measurableSet_transported_qORegion X g k)

end LeanFormal.IUT.N8Closure.EtaTensorStandardBorelActual