import tmp.sheaf.xif.paper.S2747C3NormalizedLogVolumeActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal

namespace LeanFormal.IUT.XiFPaper.S2747NormalizedHaarConfirmation

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2744PerPlaceRegionAllCoordsActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2741ComparisonVolumeEqLogGenericActual
open LeanFormal.IUT.XiFPaper.S2747C3NormalizedLogVolumeActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance s2747cMeas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance s2747cBorel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- The q-pilot normalized region log-volume is computed by the normalized Haar
    attached to the tensor lattice (which has measure one). -/
theorem c3NormalizedComparisonRegionLogVolume_eq_normalizedHaarLog :
    c3NormalizedComparisonRegionLogVolume (l := l) (V := V) (I := I) C3 T e =
      (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal := rfl

theorem c3NormalizedTensorHaar_tensorLattice_eq_one :
    c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (tensorLattice (p := C3.p)
        (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)) = 1 := by
  exact c3TensorLattice_self_measure (l := l) (V := V) (I := I) C3

#check c3NormalizedComparisonRegionLogVolume_eq_normalizedHaarLog
#check c3NormalizedTensorHaar_tensorLattice_eq_one

end LeanFormal.IUT.XiFPaper.S2747NormalizedHaarConfirmation
