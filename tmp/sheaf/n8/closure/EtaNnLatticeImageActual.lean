import tmp.sheaf.n8.closure.EtaTensorHullMeasureActual
import tmp.sheaf.n8.closure.EtaTensorHullMeasureFormulaActual

/-!
# EtaNnLatticeImageActual

Image identity `nnLattice g k = tau.symm '' qORegion (g^k)` and the transported
Haar measure formula.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaNnLatticeImageActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.EtaTensorHullMeasureActual
open LeanFormal.IUT.N8Closure.EtaTensorHullMeasureFormulaActual
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

theorem nnLattice_eq_image (g : Kf X) (k : ℕ) :
    nnLattice X g k = (tau X).symm '' qORegion X (g ^ k) := by
  ext y
  constructor
  · rintro ⟨o, rfl⟩
    refine ⟨(g ^ k) * (o : Kf X), ?_, ?_⟩
    · exact ⟨o, by simp⟩
    · rw [LinearEquiv.symm_apply_eq]
      exact (tau_tprod X (fun _ : Unit => g ^ k * (o : Kf X))).symm
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨o, -, rfl⟩
    refine ⟨o, ?_⟩
    change PiTensorProduct.tprod (ℚ_[nativePrime X])
      (fun _ : Unit => g ^ k * (o : Kf X)) =
      (tau X).symm (g ^ k * (o : Kf X))
    rw [eq_comm, LinearEquiv.symm_apply_eq]
    exact (tau_tprod X (fun _ : Unit => g ^ k * (o : Kf X))).symm

theorem measurable_tau_symm : Measurable (tau X).symm := by
  rw [measurable_iff_comap_le]
  exact MeasurableSpace.comap_le_iff_le_map.mpr le_rfl

theorem tensorHaar_nnLattice_formula (g : Kf X) (hg : g ≠ 0) (k : ℕ)
    (hmeas : MeasurableSet ((tau X).symm '' qORegion X (g ^ k))) :
    tensorHaar X (nnLattice X g k) =
      ENNReal.ofReal ((‖g‖ ^ k) ^
        (Module.finrank ℚ_[nativePrime X] (Kf X))) *
        (Measure.addHaar : Measure (Kf X)) (Integers (Kf X) : Set (Kf X)) := by
  rw [nnLattice_eq_image]
  have hf : Measurable (tau X).symm := measurable_tau_symm X
  rw [tensorHaar, Measure.map_apply hf hmeas]
  rw [Set.preimage_image_eq _ (tau X).symm.injective]
  exact qORegion_gpow_measure X g hg k

/-- Exact missing measurable-image step for the transported measure. -/
def MissingTransportedMeasurableImage (X : N8NativeInput l) : Prop :=
  ∀ (g : Kf X) (k : ℕ),
    MeasurableSet ((tau X).symm '' qORegion X (g ^ k))

end LeanFormal.IUT.N8Closure.EtaNnLatticeImageActual