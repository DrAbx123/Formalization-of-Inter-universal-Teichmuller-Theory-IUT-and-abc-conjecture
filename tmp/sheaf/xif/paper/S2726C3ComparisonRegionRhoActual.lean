import tmp.sheaf.xif.paper.S2726ComparisonRegionRhoGeneric
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S2726C3ComparisonRegionRhoActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2726ComparisonRegionRhoGeneric

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable [∀ i, Norm (C3LogShellFiber C3 i)]
variable (rho : C3.tensorIndex → ℝ)

/-- Local-component comparison region (tuple form). -/
noncomputable def S2726C3LocalComparisonRegionRhoUpper :
    Set ((i : C3.tensorIndex) → C3LogShellFiber C3 i) :=
  comparisonRegionRhoUpper rho

noncomputable def S2726C3LocalComparisonRegionRho :
    Set ((i : C3.tensorIndex) → C3LogShellFiber C3 i) :=
  comparisonRegionRho rho

#check S2726C3LocalComparisonRegionRhoUpper
end LeanFormal.IUT.XiFPaper.S2726C3ComparisonRegionRhoActual
end
