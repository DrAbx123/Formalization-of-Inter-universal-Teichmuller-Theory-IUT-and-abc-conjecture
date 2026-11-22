import tmp.sheaf.n8.closure.EtaNNOrbitHullBoundActual
import tmp.sheaf.n8.closure.EtaTensorNaturalityActual

/-!
# EtaTensorHullMeasureActual

Transport the Kf measurable space and Haar measure to the one-factor tensor
block via `tau = PiTensorProduct.subsingletonEquiv`.  The lattice measure
formula reduces to the actual Kf q-volume; the exact remaining
measurability/transport step is recorded.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaTensorHullMeasureActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaTensorSplitActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphCertificateActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismActual3
open LeanFormal.IUT.N8Closure.EtaTensorNaturalityActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismInterfaceActual
open LeanFormal.IUT.N8Closure.EtaOrbitNonnegativeBounded
open LeanFormal.IUT.N8Closure.EtaNNOrbitHullBoundActual
open LeanFormal.IUT.N8Closure.FiniteObservationHull
open LeanFormal.IUT.N8Closure.EtaTensorZpSubmoduleLatticeActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open MeasureTheory
open scoped NNReal ENNReal Pointwise NormedField TensorProduct

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X
abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)
abbrev g0 : Kf X := gNonIntegral X

local instance : MeasurableSpace (E X) :=
  MeasurableSpace.map (tau X).symm (inferInstance : MeasurableSpace (Kf X))

noncomputable def tensorHaar : Measure (E X) :=
  Measure.map (tau X).symm (Measure.addHaar : Measure (Kf X))

/-- Exact missing lattice-measure formula: the transported Haar measure of the
actual `g^k * Integers` tensor lattice. -/
def MissingNnLatticeMeasureFormula (X : N8NativeInput l) : Prop :=
  ∀ (g : Kf X) (hg : g ≠ 0) (k : ℕ),
    tensorHaar X (nnLattice X g k) =
      ENNReal.ofReal ((‖g‖ ^ k) ^
        (Module.finrank ℚ_[nativePrime X] (Kf X))) *
        (Measure.addHaar : Measure (Kf X)) (Integers (Kf X) : Set (Kf X))

end LeanFormal.IUT.N8Closure.EtaTensorHullMeasureActual