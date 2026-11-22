import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSignedLogVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticIQHull

/-!
# C6 actual IQ data on the arithmetic tensor tuple block

Carrier is ArithmeticTensorTupleBlock; hull/log-volume are actual IQ donors.
-/

namespace LeanFormal.IUT.N8C6ActualIQ

open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {iota : Type v} [Fintype iota] {V : iota → Type w}
variable (places : (i : iota) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : iota) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]

abbrev C6IQCarrier : Type (max u v) := ArithmeticTensorTupleBlock places tuple

structure C6ActualIQData where
  hull : Set (C6IQCarrier places tuple) := arithmeticTupleCanonicalHull places tuple
  iqInterface : IQHullLogVolumeInterface (C6IQCarrier places tuple) :=
    arithmeticTupleIQHullLogVolumeInterface places tuple mu
  signedHullLog : ℝ := arithmeticTupleCanonicalHullHaarLog places tuple mu
  normalizedLogVolume : Set (C6IQCarrier places tuple) → ℝ :=
    arithmeticTupleNormalizedLogVolume places tuple mu
  /-- Signed log of the canonical unit reference. -/
  unitReferenceLog : ℝ :=
    Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal
  normalizationWeight : ℝ :=
    1 / (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : ℝ)

noncomputable def C6ActualIQData.actual : C6ActualIQData places tuple mu where
  hull := arithmeticTupleCanonicalHull places tuple
  iqInterface := arithmeticTupleIQHullLogVolumeInterface places tuple mu
  signedHullLog := arithmeticTupleCanonicalHullHaarLog places tuple mu
  normalizedLogVolume := arithmeticTupleNormalizedLogVolume places tuple mu
  unitReferenceLog := Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal
  normalizationWeight :=
    1 / (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : ℝ)

end
end LeanFormal.IUT.N8C6ActualIQ