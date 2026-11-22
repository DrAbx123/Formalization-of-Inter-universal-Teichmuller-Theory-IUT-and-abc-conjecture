import tmp.sheaf.xif.paper.S2857C3ComparisonMeasureLogVolumeDataActual
import tmp.sheaf.xif.paper.S2855C3LatticeRegionLogVolumeSummaryActual
import tmp.sheaf.xif.paper.S2856C3RegionMeasureComparisonOfRealActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2858C3ComparisonMeasureLogVolumeConsumerActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2853C3RegionMeasureComparisonDataActual
open LeanFormal.IUT.XiFPaper.S2855C3LatticeRegionLogVolumeSummaryActual
open LeanFormal.IUT.XiFPaper.S2856C3RegionMeasureComparisonOfRealActual
open LeanFormal.IUT.XiFPaper.S2857C3ComparisonMeasureLogVolumeDataActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measBC : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelBC : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
 
end LeanFormal.IUT.XiFPaper.S2858C3ComparisonMeasureLogVolumeConsumerActual
end
