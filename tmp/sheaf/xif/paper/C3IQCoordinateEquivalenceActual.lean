import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology

/-!
# Actual coordinate equivalence for the C3 log-shell tensor packet

The C3 tensor block is the actual tensor product
`FinitePadicTensor` of the C3 local completions.  Using the actual product
basis (`finitePadicTensorCoordinates`), this file constructs the minimal
actual coordinate equivalence to the product of coefficient spaces over
`ℚ_[p]`, and proves that the actual tensor region and its actual Q-span map
to the corresponding region and span.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.C3IQCoordinateEquivalenceActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- Actual product-basis coordinate equivalence for the C3 tensor block. -/
noncomputable def c3LogShellTensorCoordinates :
    C3LogShellTensorBlock C3 ≃ₗ[ℚ_[C3.p]]
      (FinitePadicTensorIndex (p := C3.p)
        (fun i : C3.tensorIndex => C3LogShellFiber C3 i) → ℚ_[C3.p]) :=
  finitePadicTensorCoordinates (p := C3.p)
    (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)

/-- The same coordinate equivalence as a ℚ-linear equivalence. -/
noncomputable def c3LogShellTensorCoordinatesRat :
    C3LogShellTensorBlock C3 ≃ₗ[ℚ]
      (FinitePadicTensorIndex (p := C3.p)
        (fun i : C3.tensorIndex => C3LogShellFiber C3 i) → ℚ_[C3.p]) :=
  (c3LogShellTensorCoordinates C3).restrictScalars ℚ

/-- Coordinate formula on the actual tensor product: product of the local
product-basis coefficients. -/
theorem c3LogShellTensorCoordinates_tprod
    (x : (i : C3.tensorIndex) → C3LogShellFiber C3 i)
    (j : FinitePadicTensorIndex (p := C3.p)
      (fun i : C3.tensorIndex => C3LogShellFiber C3 i)) :
    c3LogShellTensorCoordinates C3
        (finitePadicTensorTprod (p := C3.p)
          (fun i : C3.tensorIndex => C3LogShellFiber C3 i) x) j =
      ∏ i, (Module.finBasis ℚ_[C3.p] (C3LogShellFiber C3 i)).repr
        (x i) (j i) := by
  exact finitePadicTensorCoordinates_tprod (p := C3.p)
    (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i) x j

/-- The actual Q-span maps to the Q-span of the coordinate region. -/
theorem c3LogShellTensorCoordinates_iq_span :
    Submodule.map (c3LogShellTensorCoordinatesRat C3).toLinearMap
        (actualC3LogShellTensorIQ C3) =
      Submodule.span ℚ
        (c3LogShellTensorCoordinatesRat C3 ''
          actualC3LogShellTensorRegion C3) := by
  unfold actualC3LogShellTensorIQ
  exact Submodule.map_span (c3LogShellTensorCoordinatesRat C3).toLinearMap _

end LeanFormal.IUT.XiFPaper.C3IQCoordinateEquivalenceActual
end
