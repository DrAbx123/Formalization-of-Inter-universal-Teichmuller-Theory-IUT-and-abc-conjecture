import tmp.sheaf.xif.paper.S2745C3RegionAllFiniteActual
import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.S2921C3TensorBlockScalingGenericActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2831C3RegionUnitInvarianceSummaryActual

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

local instance measAL : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelAL : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩


theorem C3Region_unit_invariance_summary
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))]
    (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
    (w : (PadicInt C3.p)ˣ) :
    IsCompact ((fun x : C3LogShellTensorBlock C3 =>
        ((unitQHom (p := C3.p) w : ℚ_[C3.p]) • x)) ''
        C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) ∧
      c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        ((fun x : C3LogShellTensorBlock C3 =>
          ((unitQHom (p := C3.p) w : ℚ_[C3.p]) • x)) ''
          C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) =
        c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
          (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) ∧
      (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
        ((fun x : C3LogShellTensorBlock C3 =>
          ((unitQHom (p := C3.p) w : ℚ_[C3.p]) • x)) ''
          C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal =
        (haarLogVolume (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
          (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e)).toReal := by
  haveI hAdd : MeasureTheory.Measure.IsAddHaarMeasure
      (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3) :=
    c3NormalizedTensorHaar_isAddHaarMeasure (l := l) (V := V) (I := I) C3
  haveI hReg : MeasureTheory.Measure.Regular
      (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3) :=
    c3NormalizedTensorHaar_regular (l := l) (V := V) (I := I) C3
  have hcont : Continuous (fun x : C3LogShellTensorBlock C3 =>
      ((unitQHom (p := C3.p) w : ℚ_[C3.p]) • x)) :=
    continuous_const_smul _
  have hcomp := C3PerPlaceUpdateRegionAll_compact (l := l) (V := V) (I := I) C3 T e
  have hcompact : IsCompact ((fun x : C3LogShellTensorBlock C3 =>
      ((unitQHom (p := C3.p) w : ℚ_[C3.p]) • x)) ''
      C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) :=
    hcomp.image hcont
  have hchar : (distribHaarChar (C3LogShellTensorBlock C3)
      (unitQHom (p := C3.p) w) : ENNReal) = 1 :=
    congrArg (fun r : NNReal => (r : ENNReal))
      (tensor_unit_char_eq_one (p := C3.p)
        (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i) w)
  have hmeas : c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      ((fun x : C3LogShellTensorBlock C3 =>
        ((unitQHom (p := C3.p) w : ℚ_[C3.p]) • x)) ''
        C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) =
      c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
        (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e) := by
    rw [c3TensorBlock_scaling_generic
      (μ := c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
      (l := l) (V := V) (I := I) C3 T e (unitQHom (p := C3.p) w)
      (C3PerPlaceUpdateRegionAll (l := l) (V := V) (I := I) C3 T e), hchar, one_mul]
  refine ⟨hcompact, hmeas, ?_⟩
  unfold haarLogVolume
  rw [hmeas]

#check C3Region_unit_invariance_summary

end LeanFormal.IUT.XiFPaper.S2831C3RegionUnitInvarianceSummaryActual
end
