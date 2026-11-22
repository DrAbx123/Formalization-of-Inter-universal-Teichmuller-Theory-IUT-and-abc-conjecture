import tmp.sheaf.n8.closure.P6TensorToGlobalBridgeAttempt
import tmp.sheaf.n8.closure.P6Comparison
import tmp.sheaf.n8.closure.P6L

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# Global Adm construction from tensor bridge / J.region

Attempts to construct the actual Adm reference/region and procession
weights/dimensions from the C4/C6 data of a `SourceAllowedOutput` J.

From a `TensorToGlobalBridge J` we can project its donor fields, and from the
actual map we can form the image of J.region.  But J.region/C6 data alone does
not contain a reference region, positive finite masses, a.e. zero local logs,
support, weights or dimensions.  No actual global Adm construction exists;
the exact target is recorded as a named gap.  No arbitrary Adm is produced.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6TensorToGlobalBridgeAttempt

namespace LeanFormal.IUT.N8Closure.P6TensorGlobalAdmConstruction

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Exact missing global Adm/readout data: actual reference/region family,
Adm, support, weights and nonzero dimensions with ellOut equal to J.ellOut. -/
def AdmConstructionTarget
    (J : P6Comparison.SourceAllowedOutput X) : Prop :=
  ∃ (reference region : GlobalRegion X)
    (support : Finset (NativePlaces X.S))
    (weight dimension : NativePlaces X.S → ℝ),
    (∀ v : NativePlaces X.S, dimension v ≠ 0) ∧
      P6L.Adm (X := X) (mu := mu) reference region ∧
        P6L.ellOut (X := X) (mu := mu) support weight dimension
          reference region = J.ellOut

/-- The global image of J.region under the actual tensor-to-global map. -/
def globalRegionImage
    (J : P6Comparison.SourceAllowedOutput X)
    (B : TensorToGlobalBridge (X := X) (mu := mu) J) : GlobalRegion X :=
  fun v => {x | ∃ y ∈ J.region, B.toGlobal y v = x}

/-- The image region is contained in the bridge's global region. -/
theorem globalRegionImage_subset_bridgeRegion
    (J : P6Comparison.SourceAllowedOutput X)
    (B : TensorToGlobalBridge (X := X) (mu := mu) J) :
    ∀ v : NativePlaces X.S,
      globalRegionImage (X := X) (mu := mu) J B v ⊆ B.region v := by
  intro v x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact B.toGlobal_mem_region y hy v

/-- A TensorToGlobalBridge already supplies the exact Adm construction data. -/
theorem admConstructionTarget_of_tensorBridge
    (B : TensorToGlobalBridge (X := X) (mu := mu) J) :
    AdmConstructionTarget (X := X) (mu := mu) J := by
  exact ⟨B.reference, B.region, B.support, B.weight, B.dimension,
    B.dimension_ne_zero, B.adm, B.ellOut_eq⟩

end LeanFormal.IUT.N8Closure.P6TensorGlobalAdmConstruction

end