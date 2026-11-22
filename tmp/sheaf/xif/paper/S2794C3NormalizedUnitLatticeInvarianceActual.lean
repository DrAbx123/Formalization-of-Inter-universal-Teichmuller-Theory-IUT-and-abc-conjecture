import tmp.sheaf.xif.paper.S2746C3NormalizedHaarActual
import tmp.sheaf.xif.paper.S2736cTensorLatticeActual
import tmp.sheaf.xif.paper.S2921C3TensorBlockScalingGenericActual
import tmp.sheaf.xif.paper.C3NormalizedHaarInstancesActual
import tmp.sheaf.xif.paper.C3LogShellTensorInstancesActual

noncomputable section
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 800000
open scoped BigOperators NNReal ENNReal
namespace LeanFormal.IUT.XiFPaper.S2794C3NormalizedUnitLatticeInvarianceActual

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
open LeanFormal.IUT.XiFPaper.PrimeStripLogShellActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
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

local instance measM : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance borelM : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

local instance instFiberNormed :
    ∀ i, NormedAddCommGroup (C3LogShellFiber C3 i) := fun i => inferInstance
local instance instFiberNormedSpace :
    ∀ i, NormedSpace ℚ_[C3.p] (C3LogShellFiber C3 i) := fun i => inferInstance
local instance instFiberFiniteDim :
    ∀ i, FiniteDimensional ℚ_[C3.p] (C3LogShellFiber C3 i) := fun i => inferInstance

theorem c3NormalizedTensorHaar_unit_smul_lattice
    (T : SourceNativeInitialThetaData.{0} fiveLabel)
    [Fintype (Bad (nativePlaceSelection T))]
    (e : C3.tensorIndex ≃ Bad (nativePlaceSelection T))
    (w : (PadicInt C3.p)ˣ) :
    c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3
      ((fun x : C3LogShellTensorBlock C3 =>
        ((unitQHom (p := C3.p) w : ℚ_[C3.p]) • x)) ''
        (tensorLattice (p := C3.p)
          (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i) :
          Set (C3LogShellTensorBlock C3))) = 1 := by
  haveI hAdd : MeasureTheory.Measure.IsAddHaarMeasure
      (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3) :=
    c3NormalizedTensorHaar_isAddHaarMeasure (l := l) (V := V) (I := I) C3
  haveI hReg : MeasureTheory.Measure.Regular
      (c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3) :=
    c3NormalizedTensorHaar_regular (l := l) (V := V) (I := I) C3
  have hchar : (distribHaarChar (C3LogShellTensorBlock C3)
      (unitQHom (p := C3.p) w) : ENNReal) = 1 :=
    congrArg (fun r : NNReal => (r : ENNReal))
      (tensor_unit_char_eq_one (p := C3.p)
        (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i) w)
  rw [c3TensorBlock_scaling_generic
      (μ := c3NormalizedTensorHaar (l := l) (V := V) (I := I) C3)
      (l := l) (V := V) (I := I) C3 T e (unitQHom (p := C3.p) w)
      (tensorLattice (p := C3.p)
        (M := fun i : C3.tensorIndex => C3LogShellFiber C3 i)),
    c3TensorLattice_self_measure (l := l) (V := V) (I := I) C3, hchar, one_mul]

#check c3NormalizedTensorHaar_unit_smul_lattice
end LeanFormal.IUT.XiFPaper.S2794C3NormalizedUnitLatticeInvarianceActual
end
