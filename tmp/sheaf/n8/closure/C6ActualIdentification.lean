import tmp.sheaf.n8.closure.C6ActualIQData
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface

/-!
# C6ActualIQData actual-identification

`C6ActualIQData` has default-valued fields, so an arbitrary `B` need not be the
actual donor instance.  This file records the exact identification equalities and
proves that `C6ActualIQData.actual` satisfies them.
-/

noncomputable section

namespace LeanFormal.IUT.N8C6ActualIQ

open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {iota : Type v} [Fintype iota] {V : iota → Type w}
variable (places : (i : iota) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : iota) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]

structure C6ActualIQData.IsActual (B : C6ActualIQData places tuple mu) : Prop where
  hull_eq : B.hull = arithmeticTupleCanonicalHull places tuple
  iqInterface_eq : B.iqInterface = arithmeticTupleIQHullLogVolumeInterface places tuple mu
  signedHullLog_eq : B.signedHullLog = arithmeticTupleCanonicalHullHaarLog places tuple mu
  normalizedLogVolume_eq :
    B.normalizedLogVolume = arithmeticTupleNormalizedLogVolume places tuple mu
  unitReferenceLog_eq :
    B.unitReferenceLog = Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal
  normalizationWeight_eq :
    B.normalizationWeight = 1 / (Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple) : ℝ)

theorem C6ActualIQData.actual_isActual :
    (C6ActualIQData.actual places tuple mu).IsActual := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end LeanFormal.IUT.N8C6ActualIQ