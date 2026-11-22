import tmp.sheaf.n8.closure.EtaNontriviallyNormedKfActual
import tmp.sheaf.n8.closure.EtaFPlaceDVRUniformizerDataActual
import tmp.sheaf.n8.closure.EtaDVRInstanceActual
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaNontriviallyNormedKfActual
open LeanFormal.IUT.N8Closure.EtaFPlaceDVRUniformizerDataActual
open LeanFormal.IUT.N8Closure.EtaDVRInstanceActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open MeasureTheory Metric
open scoped NNReal ENNReal NormedField Pointwise
variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X
abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)
example : 0 < (Measure.addHaar : Measure (LeanFormal.IUT.N8Closure.EtaFPlaceDVRUniformizerDataActual.Kf X)) (Integers (LeanFormal.IUT.N8Closure.EtaFPlaceDVRUniformizerDataActual.Kf X) : Set (LeanFormal.IUT.N8Closure.EtaFPlaceDVRUniformizerDataActual.Kf X)) := by
  apply Measure.measure_pos_of_nonempty_interior
  refine ⟨0, ?_⟩
  rw [mem_interior_iff_mem_nhds]
  apply _root_.mem_nhds_iff.mpr
  refine ⟨Metric.ball (0 : LeanFormal.IUT.N8Closure.EtaFPlaceDVRUniformizerDataActual.Kf X) 1, ?_, isOpen_ball, mem_ball_self one_pos⟩
  intro x hx
  rw [mem_integers_iff]
  have hx' : ‖x - 0‖ < 1 := hx
  simpa using hx'.le

example : (Measure.addHaar : Measure (LeanFormal.IUT.N8Closure.EtaFPlaceDVRUniformizerDataActual.Kf X)) (Integers (LeanFormal.IUT.N8Closure.EtaFPlaceDVRUniformizerDataActual.Kf X) : Set (LeanFormal.IUT.N8Closure.EtaFPlaceDVRUniformizerDataActual.Kf X)) < ∞ := by
  exact (isCompact_iff_compactSpace.mp (EtaDVRInstanceActual.integersCompactSpace (X:=X))).measure_lt_top
