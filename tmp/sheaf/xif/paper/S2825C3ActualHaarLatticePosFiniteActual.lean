import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.S2756C3HaarNormalizationBridgeActual
import tmp.sheaf.xif.paper.S2811C3LatticeHaarSummaryActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2825C3ActualHaarLatticePosFiniteActual

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
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2756C3HaarNormalizationBridgeActual
open LeanFormal.IUT.XiFPaper.S2811C3LatticeHaarSummaryActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measAH : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelAH : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩
local instance actualAddInv : MeasureTheory.Measure.IsAddLeftInvariant
    (actualC3LogShellTensorHaar C3) := by
  unfold actualC3LogShellTensorHaar
  infer_instance
local instance actualReg : MeasureTheory.Measure.Regular
    (actualC3LogShellTensorHaar C3) := by
  unfold actualC3LogShellTensorHaar
  infer_instance
local instance normAddInv : MeasureTheory.Measure.IsAddLeftInvariant
    (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3) := by
  unfold c3NormalizedTensorHaar
  infer_instance
local instance normReg : MeasureTheory.Measure.Regular
    (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3) :=
  c3NormalizedTensorHaar_regular (l := l) (V := V) (I := I) C3

theorem C3ActualHaar_tensorLattice_pos_finite :
    0 < actualC3LogShellTensorHaar C3
        ((c3TensorLatticeCompacts (l := l) (V := V) (I := I) C3 :
          TopologicalSpace.PositiveCompacts (C3LogShellTensorBlock C3)) :
          Set (C3LogShellTensorBlock C3)) ∧
      actualC3LogShellTensorHaar C3
        ((c3TensorLatticeCompacts (l := l) (V := V) (I := I) C3 :
          TopologicalSpace.PositiveCompacts (C3LogShellTensorBlock C3)) :
          Set (C3LogShellTensorBlock C3)) < ⊤ := by
  have hfin : actualC3LogShellTensorHaar C3
      ((c3TensorLatticeCompacts (l := l) (V := V) (I := I) C3 :
        TopologicalSpace.PositiveCompacts (C3LogShellTensorBlock C3)) :
        Set (C3LogShellTensorBlock C3)) < ⊤ :=
    (C3LatticeHaar_actual_finite_and_normalized_one (l := l) (V := V) (I := I) C3).1
  have hnorm : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      ((c3TensorLatticeCompacts (l := l) (V := V) (I := I) C3 :
        TopologicalSpace.PositiveCompacts (C3LogShellTensorBlock C3)) :
        Set (C3LogShellTensorBlock C3)) = 1 :=
    (C3LatticeHaar_actual_finite_and_normalized_one (l := l) (V := V) (I := I) C3).2
  have hscale := c3NormalizedTensorHaar_apply_eq_smul_actual (l := l) (V := V) (I := I) C3
    ((c3TensorLatticeCompacts (l := l) (V := V) (I := I) C3 :
      TopologicalSpace.PositiveCompacts (C3LogShellTensorBlock C3)) :
      Set (C3LogShellTensorBlock C3))
  refine ⟨pos_iff_ne_zero.mpr ?_, hfin⟩
  intro hzero
  rw [hzero, mul_zero] at hscale
  rw [hnorm] at hscale
  exact one_ne_zero hscale

#check C3ActualHaar_tensorLattice_pos_finite
end LeanFormal.IUT.XiFPaper.S2825C3ActualHaarLatticePosFiniteActual
end
