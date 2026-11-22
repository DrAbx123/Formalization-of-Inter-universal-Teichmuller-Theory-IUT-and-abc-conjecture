import tmp.sheaf.n8.closure.P6WeightedIndexBridgeAttempt
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSelectedPrimeWeightedVolume

/-!
# Tuple-indexed selected-prime weights -> NativePlaces bridge attempt

Actual partial bridge: a tuple `ι -> FinitePlaceAtPrime Fmod p` maps to the
finite set of native selected places given by the Wave12 finite-place bridge.

Selected-prime weights (`selectedPrimeTupleDegree`, tuple-block finrank) are
per-tuple data, not per-native-place data.  No production finite tuple family,
canonical per-place aggregation, or nonzero aggregate dimension is available.
The exact `ProcessionWeightDimensionDonor` target is therefore registered with
a named sorry; no arbitrary weights are chosen.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.P6ProcessionWeightDonorActual
open LeanFormal.IUT.N8Closure.P6WeightedIndexBridgeAttempt

namespace LeanFormal.IUT.N8Closure.P6WeightedTupleIndexBridge

universe u v

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {p : ℕ} [Fact p.Prime] {ι : Type v} [Fintype ι]

/-- Actual tuple-index bridge to the finite set of native places. -/
noncomputable def tupleNativeSupport
    (tuple : ι → FinitePlaceAtPrime (X.S.arithmetic.Fmod) p) :
    Finset (NativePlaces X.S) := by
  classical
  exact Finset.univ.image (fun i =>
    nativePlaceOfFinitePlace X (tuple i).val)

theorem mem_tupleNativeSupport_iff
    (tuple : ι → FinitePlaceAtPrime (X.S.arithmetic.Fmod) p)
    (v : NativePlaces X.S) :
    v ∈ tupleNativeSupport (X := X) (p := p) tuple ↔
      ∃ i : ι, nativePlaceOfFinitePlace X (tuple i).val = v := by
  classical
  simp [tupleNativeSupport]

/-- The exact target remains the actual native-place weight/dimension donor. -/
abbrev TupleWeightBridgeDonorTarget : Prop :=
  ProcessionWeightDimensionDonorActualTarget (X := X)

/-! ## Exact no-go for the per-place weight/dimension

- selected-prime weights are functions of the whole tuple, not of a single
  `NativePlace`;
- no production finite tuple family/support is selected;
- no production nonzero aggregate dimension on `NativePlaces` is constructed;
- hence the tuple index bridge gives only finite supports, not the actual
  `ProcessionWeightDimensionDonor`.  Named sorry remains, no arbitrary weights.
-/

end LeanFormal.IUT.N8Closure.P6WeightedTupleIndexBridge