import tmp.sheaf.n8.closure.C6ActualIQData
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.C9ValuesBoundedPositive

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8C6ActualIQ
open MeasureTheory

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type} [Fintype iota] {V : iota → Type} [∀ i, Fintype (V i)]
variable (places : (i : iota) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : iota) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]

/-- Positive-mass ValuesBounded for the actual C6 normalized log-volume. -/
def ValuesBoundedPos
    (B : C6ActualIQData places tuple mu)
    (ThetaLog : ℝ)
    (provenance : Set (Set (C6IQCarrier places tuple))) : Prop :=
  ∀ S : Set (C6IQCarrier places tuple),
    S ∈ provenance →
    0 < mu S →
    S ⊆ B.hull →
    B.normalizedLogVolume S ≤ ThetaLog

theorem valuesBoundedPos_actual :
    ValuesBoundedPos places tuple mu
      (C6ActualIQData.actual places tuple mu)
      ((C6ActualIQData.actual places tuple mu).normalizedLogVolume
        (arithmeticTupleCanonicalHull places tuple))
      {S | S ⊆ arithmeticTupleCanonicalHull places tuple} := by
  intro S _hmem hSpos hS
  have hTfin := (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.2
  have hmono := arithmeticTupleNormalizedLogVolume_mono places tuple mu
    (S := S) (T := arithmeticTupleCanonicalHull places tuple) hS hSpos hTfin
  simpa [C6ActualIQData.actual] using hmono

end LeanFormal.IUT.N8Closure.C9ValuesBoundedPositive

end
