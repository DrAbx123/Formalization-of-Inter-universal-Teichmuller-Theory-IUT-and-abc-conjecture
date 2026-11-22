/- Small actual producer attempt: hullLog = -nativeGlobalQPilotNormalizedLogMagnitude. -/
import tmp.sheaf.xif.paper.Mzk1IVThm110FloorNativeHullActual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1P8HullLogProducerActual

open MeasureTheory MeasureTheory.Measure
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple)) [μ.IsAddHaarMeasure]
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Attempt: actual canonical hull log equals -M from actual hull data. -/
theorem actual_hullLog_eq_neg_M :
    arithmeticTupleCanonicalHullHaarLog places tuple μ =
      -nativeGlobalQPilotNormalizedLogMagnitude T := by
  unfold arithmeticTupleCanonicalHullHaarLog
  rfl

#check actual_hullLog_eq_neg_M
end LeanFormal.IUT.XiFPaper.Mzk1G1P8HullLogProducerActual
end
