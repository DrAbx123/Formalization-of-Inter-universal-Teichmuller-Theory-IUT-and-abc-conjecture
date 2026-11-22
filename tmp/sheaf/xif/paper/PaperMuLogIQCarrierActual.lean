import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import tmp.sheaf.n8.closure.C6ActualIQData

-- Actual paper μ_log/Haar volume on the actual IQ carrier.
--
-- The existing actual IQ carrier is the finite-place arithmetic tensor block
-- ArithmeticTensorTupleBlock places tuple. Its actual Haar log-volume
-- interface is arithmeticTupleIQHullLogVolumeInterface, with
-- logVolume = haarLogVolume μ on the actual additive Haar measure μ.
-- This file packages that actual object as the paper μ_log on the IQ carrier.
-- No new measure, shell, or fake normalization is invented.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperMuLogIQCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8C6ActualIQ
open MeasureTheory

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure μ]

-- The actual IQ carrier.
abbrev PaperIQCarrier : Type (max u v) :=
  ArithmeticTensorTupleBlock places tuple

-- The actual paper μ_log interface on the IQ carrier.
noncomputable def paperMuLogIQCarrier :
    IQHullLogVolumeInterface (PaperIQCarrier (places := places) (tuple := tuple)) :=
  arithmeticTupleIQHullLogVolumeInterface places tuple μ

-- The actual Haar log-volume functional.
noncomputable def paperMuLogHaar (S : Set (PaperIQCarrier (places := places) (tuple := tuple))) :
    ENNReal :=
  haarLogVolume μ S

theorem paperMuLogIQCarrier_logVolume :
    (paperMuLogIQCarrier places tuple μ).logVolume = paperMuLogHaar places tuple μ :=
  arithmeticTupleIQHullLogVolumeInterface_logVolume places tuple μ

theorem paperMuLogIQCarrier_hull :
    (paperMuLogIQCarrier places tuple μ).hull =
      arithmeticTupleCanonicalHull places tuple :=
  arithmeticTupleIQHullLogVolumeInterface_hull places tuple μ

theorem paperMuLogIQCarrier_unitRegion :
    (paperMuLogIQCarrier places tuple μ).unitRegion =
      arithmeticTupleCanonicalHull places tuple :=
  arithmeticTupleIQHullLogVolumeInterface_unitRegion places tuple μ

-- The C6 actual IQ data uses exactly this paper μ_log interface.
theorem paperMuLogIQCarrier_eq_C6IQInterface :
    paperMuLogIQCarrier places tuple μ =
      (C6ActualIQData.actual places tuple μ).iqInterface := rfl

-- Hull finiteness in the actual interface.
theorem paperMuLogIQCarrier_hull_lt_top :
    (paperMuLogIQCarrier places tuple μ).logVolume
      (paperMuLogIQCarrier places tuple μ).hull < ⊤ :=
  arithmeticTupleIQHullLogVolumeInterface_hull_lt_top places tuple μ

#check paperMuLogIQCarrier
#check paperMuLogHaar
#check paperMuLogIQCarrier_logVolume
#check paperMuLogIQCarrier_hull
#check paperMuLogIQCarrier_eq_C6IQInterface
#check paperMuLogIQCarrier_hull_lt_top

end LeanFormal.IUT.XiFPaper.PaperMuLogIQCarrierActual

end