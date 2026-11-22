import tmp.sheaf.n8.closure.P6ReadoutCarrierFromSourceAllowedAttempt
import tmp.sheaf.n8.closure.P6Comparison
import tmp.sheaf.n8.closure.P6L

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# Tensor block -> global native-place bridge attempt

The C6 source data sits on the arithmetic tensor block
`ArithmeticTensorTupleBlock J.C3.tensorPlaces J.C3.tensorTuple`.  P6Readout
needs a global family `(v : NativePlaces X.S) -> localFieldAt X v` with an
actual Adm reference/region, support and procession weights/dimensions.

No production map from the tensor block to the global native-place family
exists, and no actual Adm data/weights/dimensions are constructed.  This file
defines the exact bridge structure (map plus compatibility and the readout
data) and records its existence as a theorem-level named gap.  The map is not
a free parameter of a completed construction.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6ReadoutCarrierFromSourceAllowedAttempt

namespace LeanFormal.IUT.N8Closure.P6TensorToGlobalBridgeAttempt

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Exact bridge data from the C6 tensor block to the global native-place
family, with the readout fields it must feed.  `toGlobal_mem_region` ties the
map to the C4/T11 region; `ellOut_eq` ties the global readout to J.ellOut. -/
structure TensorToGlobalBridge
    (J : P6Comparison.SourceAllowedOutput X) where
  /-- Actual map from the C6 tensor block to the global local-field family. -/
  toGlobal : ArithmeticTensorTupleBlock J.C3.tensorPlaces J.C3.tensorTuple →
    (∀ v : NativePlaces X.S, localFieldAt X v)
  /-- Global output region. -/
  region : GlobalRegion X
  /-- The map sends J's source region into the global region family. -/
  toGlobal_mem_region : ∀ y ∈ J.region, ∀ v : NativePlaces X.S,
    toGlobal y v ∈ region v
  /-- Global reference region. -/
  reference : GlobalRegion X
  /-- Actual Adm condition. -/
  adm : P6L.Adm (X := X) (mu := mu) reference region
  /-- Finite procession support. -/
  support : Finset (NativePlaces X.S)
  /-- Procession weights. -/
  weight : NativePlaces X.S → ℝ
  /-- Local dimensions. -/
  dimension : NativePlaces X.S → ℝ
  /-- Nonzero local dimensions. -/
  dimension_ne_zero : ∀ v : NativePlaces X.S, dimension v ≠ 0
  /-- The global ell_out equals the source-allowed J ellOut. -/
  ellOut_eq : P6L.ellOut (X := X) (mu := mu) support weight dimension
      reference region = J.ellOut

/-- The exact bridge yields the per-J actual readout. -/
theorem readoutFromSourceAllowed_of_tensorBridge
    (J : P6Comparison.SourceAllowedOutput X)
    (B : TensorToGlobalBridge (X := X) (mu := mu) J) :
    ReadoutFromSourceAllowed (X := X) (mu := mu) J := by
  refine ⟨{
    support := B.support
    weight := B.weight
    dimension := B.dimension
    dimension_ne_zero := B.dimension_ne_zero
    reference := B.reference
    region := B.region
    adm := B.adm
    value := P6L.ellOut (X := X) (mu := mu)
      B.support B.weight B.dimension B.reference B.region
    value_eq := rfl }, ?_⟩
  exact B.ellOut_eq

end LeanFormal.IUT.N8Closure.P6TensorToGlobalBridgeAttempt

end