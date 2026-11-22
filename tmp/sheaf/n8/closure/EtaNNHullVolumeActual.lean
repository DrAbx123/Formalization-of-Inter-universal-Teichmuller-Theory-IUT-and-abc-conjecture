import tmp.sheaf.n8.closure.EtaTensorStandardBorelActual
import tmp.sheaf.n8.closure.EtaOrbitNonnegativeBounded

/-!
# EtaNNHullVolumeActual

Actual volume lower bounds for the finite nonnegative hull `nnOrbitSubFinite`
and the full nonnegative orbit span `nnOrbitSub`, obtained from the actual
tensor lattice measure and monotonicity.  Equality (upper bound) needs the
lattice-span identity, recorded as the exact gap.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaNNHullVolumeActual

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

theorem nnLattice_subset_finite (g : Kf X) (k : ℕ) :
    nnLattice X g k ⊆ (nnOrbitSubFinite X g k : Set (E X)) := by
  intro x hx
  exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨⟨k, Nat.lt_succ_self k⟩, hx⟩)

theorem nnLattice_subset_full (g : Kf X) (k : ℕ) :
    nnLattice X g k ⊆ (nnOrbitSub X g : Set (E X)) := by
  intro x hx
  exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨k, hx⟩)

theorem tensorHaar_nnLattice_le_finite (g : Kf X) (k : ℕ) :
    tensorHaar X (nnLattice X g k) ≤ tensorHaar X (nnOrbitSubFinite X g k) :=
  measure_mono (nnLattice_subset_finite X g k)

theorem tensorHaar_nnLattice_le_full (g : Kf X) (k : ℕ) :
    tensorHaar X (nnLattice X g k) ≤ tensorHaar X (nnOrbitSub X g) :=
  measure_mono (nnLattice_subset_full X g k)

/-- Actual lower volume bound for the finite nonnegative hull. -/
theorem nnFiniteHullVolume_lower_bound (g : Kf X) (hg : g ≠ 0) (k : ℕ) :
    ENNReal.ofReal ((‖g‖ ^ k) ^
        (Module.finrank ℚ_[nativePrime X] (Kf X))) *
        (Measure.addHaar : Measure (Kf X)) (Integers (Kf X) : Set (Kf X)) ≤
      tensorHaar X (nnOrbitSubFinite X g k) := by
  rw [← tensorHaar_nnLattice_formula_actual X g hg k]
  exact tensorHaar_nnLattice_le_finite X g k

/-- Actual lower volume bound for the full nonnegative orbit span. -/
theorem nnFullHullVolume_lower_bound (g : Kf X) (hg : g ≠ 0) (k : ℕ) :
    ENNReal.ofReal ((‖g‖ ^ k) ^
        (Module.finrank ℚ_[nativePrime X] (Kf X))) *
        (Measure.addHaar : Measure (Kf X)) (Integers (Kf X) : Set (Kf X)) ≤
      tensorHaar X (nnOrbitSub X g) := by
  rw [← tensorHaar_nnLattice_formula_actual X g hg k]
  exact tensorHaar_nnLattice_le_full X g k

/-- Exact missing hull equality/upper bound: finite hull volume equals the
largest lattice volume.  Needs `nnOrbitSubFinite g k = Lv(g^k)` or a
comparable span identity. -/
def MissingNNHullVolumeEquality (X : N8NativeInput l) : Prop :=
  ∀ (g : Kf X) (hg : g ≠ 0) (k : ℕ),
    tensorHaar X (nnOrbitSubFinite X g k) =
      ENNReal.ofReal ((‖g‖ ^ k) ^
        (Module.finrank ℚ_[nativePrime X] (Kf X))) *
        (Measure.addHaar : Measure (Kf X)) (Integers (Kf X) : Set (Kf X))

end LeanFormal.IUT.N8Closure.EtaNNHullVolumeActual