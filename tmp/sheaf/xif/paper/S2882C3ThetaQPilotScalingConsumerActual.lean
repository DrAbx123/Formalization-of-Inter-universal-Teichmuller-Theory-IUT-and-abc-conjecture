import tmp.sheaf.xif.paper.S2745C3RegionAllFiniteActual
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.S2921C3TensorBlockScalingGenericActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2882C3ThetaQPilotScalingConsumerActual

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
open LeanFormal.IUT.XiFPaper.S2726PerPlaceUpdateRegionActual
open LeanFormal.IUT.XiFPaper.S2734LatticeActual
open LeanFormal.IUT.XiFPaper.S2736cTensorLatticeActual
open LeanFormal.IUT.XiFPaper.S2736dTLCompactActual
open LeanFormal.IUT.XiFPaper.S2745C3RegionAllFiniteActual
open LeanFormal.IUT.XiFPaper.S2746C3NormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S2921C3TensorBlockScalingGenericActual
open LeanFormal.IUT.XiFPaper.C3NormalizedHaarInstancesActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorInstancesActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
variable [∀ i, NeZero (Module.finrank ℚ_[C3.p] (C3LogShellFiber C3 i))]
variable [DecidableEq C3.tensorIndex]

local instance measAE : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelAE : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3ThetaQPilot_scaling_consumer
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))]
    (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
    (u : ℚ_[C3.p]ˣ) :
    Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        ((fun x : C3LogShellTensorBlock C3 => ((u : ℚ_[C3.p]) • x)) ''
          C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) =
      Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) +
        Real.log ((distribHaarChar (C3LogShellTensorBlock C3) u : ℝ)) ∧
      0 ≤ Real.log ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal) ∧
      0 ≤ (∑ i, C3PerPlaceUpdateRho (l := l) (V := V) (I := I) C3 T e i) := by
  haveI hAdd : MeasureTheory.Measure.IsAddHaarMeasure
      (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3) :=
    c3NormalizedTensorHaar_isAddHaarMeasure (l := l) (V := V) (I := I) C3
  haveI hReg : MeasureTheory.Measure.Regular
      (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3) :=
    c3NormalizedTensorHaar_regular (l := l) (V := V) (I := I) C3
  have hscale := c3TensorBlock_scaling_generic
    (μ := c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
    (l := l) (V := V) (I := I) C3 T e u
    (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)
  have hge1 := c3NormalizedTensorHaar_hge1 (l := l) (V := V) (I := I) C3 T e
  have hne : (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hge1)
  have hcpos : (0 : ℝ) < (distribHaarChar (C3LogShellTensorBlock C3) u : ℝ) := by
    exact_mod_cast (distribHaarChar_pos (A := C3LogShellTensorBlock C3) (g := u))
  refine ⟨?_, Real.log_nonneg hge1, Finset.sum_nonneg (fun i _ =>
    C3PerPlaceUpdateRho_nonneg (l := l) (V := V) (I := I) C3 T e i)⟩
  rw [hscale, ENNReal.toReal_mul, ENNReal.coe_toReal]
  rw [mul_comm ((distribHaarChar (C3LogShellTensorBlock C3) u : ℝ))
    ((c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal)]
  rw [Real.log_mul hne (ne_of_gt hcpos)]

#check C3ThetaQPilot_scaling_consumer

end LeanFormal.IUT.XiFPaper.S2882C3ThetaQPilotScalingConsumerActual
end
