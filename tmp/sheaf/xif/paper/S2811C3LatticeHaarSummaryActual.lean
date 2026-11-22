import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.S2736cTensorLatticeActual
import tmp.sheaf.xif.paper.S2736dTLCompactActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2811C3LatticeHaarSummaryActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measR2 : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelR2 : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
local instance actualFiniteCompacts :
    IsFiniteMeasureOnCompacts (actualC3LogShellTensorHaar C3) := by
  unfold actualC3LogShellTensorHaar
  infer_instance

/-- The tensor lattice as a positive compact, avoiding direct Pi-instance
elaboration of `tensorLattice` in the statement. -/
theorem C3LatticeHaar_actual_finite_and_normalized_one :
    actualC3LogShellTensorHaar C3
        ((c3TensorLatticeCompacts (l := l) (V := V) (I := I) C3 :
          TopologicalSpace.PositiveCompacts (C3LogShellTensorBlock C3)) :
          Set (C3LogShellTensorBlock C3)) < ⊤ ∧
      c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        ((c3TensorLatticeCompacts (l := l) (V := V) (I := I) C3 :
          TopologicalSpace.PositiveCompacts (C3LogShellTensorBlock C3)) :
          Set (C3LogShellTensorBlock C3)) = 1 :=
  ⟨(c3TensorLatticeCompacts (l := l) (V := V) (I := I) C3).isCompact.measure_lt_top,
    by
      unfold c3NormalizedTensorHaar
      exact Measure.addHaarMeasure_self⟩

#check C3LatticeHaar_actual_finite_and_normalized_one
end LeanFormal.IUT.XiFPaper.S2811C3LatticeHaarSummaryActual
end
