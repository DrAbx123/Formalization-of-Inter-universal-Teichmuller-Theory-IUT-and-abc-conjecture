import tmp.sheaf.n8.closure.P6ProcessionWeightDonorActual
import tmp.sheaf.n8.closure.NativeInput
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSelectedPrimeWeightedVolume

/-!
# WeightedDeterminantPacket/selected-prime index -> NativePlaces bridge attempt

Actual partial bridge: a base finite place maps to a native selected place via
the native place bijection `V_mod_bijection`; finite supports transport.

Production weight/dimension data are not on `NativePlaces`:
- `WeightedDeterminantPacket` is indexed by an arbitrary finite `label`;
- selected-prime weights are indexed by a tuple `ι -> FinitePlaceAtPrime k p`
  and depend on the whole tuple, not on one native place.

There is no production bridge turning those into a per-NativePlaces support/
weight/dimension, so the actual `ProcessionWeightDimensionDonor` is not
constructed.  The exact target is registered with a named sorry; no arbitrary
weights are chosen.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.P6ProcessionWeightDonorActual

namespace LeanFormal.IUT.N8Closure.P6WeightedIndexBridgeAttempt

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual partial index bridge: a base finite place gives a native selected
place through `V_mod_bijection`. -/
noncomputable def nativePlaceOfFinitePlace
    (place : NumberField.FinitePlace X.S.arithmetic.Fmod) :
    NativePlaces X.S :=
  X.S.tuple.source.V_mod_bijection (NumberFieldPlace.finite place)

theorem nativePlaceOfFinitePlace_comap
    (place : NumberField.FinitePlace X.S.arithmetic.Fmod) :
    NumberFieldPlace.comap (k := X.S.arithmetic.Fmod)
      (nativePlaceOfFinitePlace X place).1 =
      NumberFieldPlace.finite place := by
  have hsymm : X.S.tuple.source.V_mod_bijection.symm
      (nativePlaceOfFinitePlace X place) = NumberFieldPlace.finite place := by
    unfold nativePlaceOfFinitePlace
    rw [Equiv.symm_apply_apply]
  exact (X.S.tuple.source.V_place_comap
    (nativePlaceOfFinitePlace X place)).trans hsymm

/-- Actual finite-support transport along the partial index bridge. -/
noncomputable def nativeSupportOfFinset
    (s : Finset (NumberField.FinitePlace X.S.arithmetic.Fmod)) :
    Finset (NativePlaces X.S) := by
  classical
  exact s.image (nativePlaceOfFinitePlace X)

/-- The exact missing target remains the actual native-place donor. -/
abbrev WeightedIndexBridgeActualTarget : Prop :=
  ProcessionWeightDimensionDonorActualTarget (X := X)

/-! ## Exact no-go for the weight/dimension bridge

- `WeightedDeterminantPacket` has no canonical finite `label -> NativePlaces`
  map; its label is an arbitrary finite type.
- Selected-prime weights live on tuple-indexed blocks; a per-NativePlaces
  weight would require choosing a tuple/support decomposition, which is not
  production data.
- Therefore the partial finite-place index bridge does not yield the actual
  weight/dimension donor; named sorry remains.
-/

end LeanFormal.IUT.N8Closure.P6WeightedIndexBridgeAttempt
