import tmp.sheaf.n8.closure.EtaNNHullVolumeActual
import tmp.sheaf.n8.closure.EtaUniformizerRelationActual

/-!
# EtaNNHullVolumeEqualityActual

Monotonicity of the nonnegative lattices for the actual nonintegral
`gNonIntegral = fPlaceP⁻¹`: `Lv(g^n) ⊆ Lv(g^(n+1))` using
`fPlaceP ∈ Integers`.  The exact hull-span/volume equality gap is recorded.
-/

set_option maxHeartbeats 4000000

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaNNHullVolumeEqualityActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaTensorHullMeasureActual
open LeanFormal.IUT.N8Closure.EtaTensorHullMeasureFormulaActual
open LeanFormal.IUT.N8Closure.EtaNnLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorStandardBorelActual
open LeanFormal.IUT.N8Closure.EtaTensorNaturalityActual
open LeanFormal.IUT.N8Closure.EtaTensorAutomorphismActual3
open LeanFormal.IUT.N8Closure.EtaTensorLatticeImageActual
open LeanFormal.IUT.N8Closure.EtaTensorGraphEdgeActual
open LeanFormal.IUT.N8Closure.EtaNNOrbitHullBoundActual
open LeanFormal.IUT.N8Closure.EtaNNHullVolumeActual
open LeanFormal.IUT.N8Closure.EtaOrbitNonnegativeBounded
open LeanFormal.IUT.N8Closure.EtaUniformizerRelationActual
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

theorem nnLattice_mono_g0 (n : ℕ) :
    nnLattice X (g0 X) n ⊆ nnLattice X (g0 X) (n + 1) := by
  rintro y ⟨o, rfl⟩
  have hmem : (fPlaceP X) * (o : Kf X) ∈ Integers (Kf X) :=
    (Integers (Kf X)).mul_mem (fPlaceP_mem_integers X) o.property
  refine ⟨⟨(fPlaceP X) * (o : Kf X), hmem⟩, ?_⟩
  apply congrArg (PiTensorProduct.tprod (ℚ_[nativePrime X]))
  funext i
  rw [pow_succ']
  have hg : (g0 X) * (fPlaceP X) = 1 := by
    rw [g0]
    exact inv_mul_cancel₀ (fPlaceP_ne_zero X)
  calc (g0 X) * (g0 X) ^ n * ((fPlaceP X) * (o : Kf X))
      = ((g0 X) * (fPlaceP X)) * ((g0 X) ^ n * (o : Kf X)) := by ring
    _ = 1 * ((g0 X) ^ n * (o : Kf X)) := by rw [hg]
    _ = (g0 X) ^ n * (o : Kf X) := by ring

/-- Exact remaining span/volume equality: needs `nnOrbitSubFinite g k` to
equal the largest lattice's span/submodule, not just contain it. -/
def MissingNNHullVolumeEqualityG0 (X : N8NativeInput l) : Prop :=
  ∀ k : ℕ,
    tensorHaar X (nnOrbitSubFinite X (g0 X) k) =
      ENNReal.ofReal ((‖(g0 X)‖ ^ k) ^
        (Module.finrank ℚ_[nativePrime X] (Kf X))) *
        (Measure.addHaar : Measure (Kf X)) (Integers (Kf X) : Set (Kf X))

end LeanFormal.IUT.N8Closure.EtaNNHullVolumeEqualityActual