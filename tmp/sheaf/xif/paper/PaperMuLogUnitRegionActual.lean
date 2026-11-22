import tmp.sheaf.xif.paper.PaperMuLogIQCarrierActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterfaceScaledUnit

/-! # Actual λ • O unit region for the paper mu_log IQ carrier

The previous paperMuLogIQCarrier used the canonical hull as its unitRegion
placeholder.  This file constructs the actual scaled unit region

  lambda • O,  lambda = arithmeticTupleIQHullUnitScale,

using the actual scaled-unit IQ interface, proves it is the actual λO region,
has positive finite Haar, and records the paper mu_log unit-region
normalization: the canonical hull is contained in lambda • O and the
logVolume/hull fields agree with paperMuLogIQCarrier.

No canonicalHull placeholder is used as the unit region.

No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperMuLogUnitRegionActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper.PaperMuLogIQCarrierActual
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

/-- The actual scaled unit region lambda • O. -/
abbrev paperMuLogActualUnitRegion :
    Set (PaperIQCarrier (places := places) (tuple := tuple)) :=
  arithmeticTupleIQHullUnitScale places tuple •
    arithmeticTupleCanonicalUnitReference places tuple

/-- The actual scaled-unit IQ interface. -/
noncomputable def paperMuLogIQCarrierActualUnitRegion :
    IQHullLogVolumeInterface
      (PaperIQCarrier (places := places) (tuple := tuple)) :=
  arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ

/-- The actual interface unit region is exactly lambda • O. -/
theorem paperMuLogIQCarrierActualUnitRegion_unitRegion :
    (paperMuLogIQCarrierActualUnitRegion places tuple μ).unitRegion =
      paperMuLogActualUnitRegion places tuple := rfl

/-- Actual positivity and finiteness of the lambda • O unit region. -/
theorem paperMuLogActualUnitRegion_measure_pos_lt_top :
    0 < μ (paperMuLogActualUnitRegion places tuple) ∧
      μ (paperMuLogActualUnitRegion places tuple) < ⊤ :=
  measure_smul_arithmeticTupleCanonicalUnitReference_pos_lt_top
    places tuple μ (arithmeticTupleIQHullUnitScale places tuple)
    (arithmeticTupleIQHullUnitScale_ne_zero places tuple)

/-- The actual lambda • O region contains the canonical hull. -/
theorem canonicalHull_subset_paperMuLogActualUnitRegion :
    arithmeticTupleCanonicalHull places tuple ⊆
      paperMuLogActualUnitRegion places tuple :=
  arithmeticTupleCanonicalHull_subset_IQHullUnitScale_smul_unitReference places tuple

/-- The actual unit region has finite log-volume in the interface. -/
theorem paperMuLogIQCarrierActualUnitRegion_unitRegion_lt_top :
    (paperMuLogIQCarrierActualUnitRegion places tuple μ).logVolume
      (paperMuLogIQCarrierActualUnitRegion places tuple μ).unitRegion < ⊤ :=
  (paperMuLogIQCarrierActualUnitRegion places tuple μ).unitRegion_logVolume_lt_top

/-- The logVolume of the scaled-unit interface is the paper mu_log Haar. -/
theorem paperMuLogIQCarrierActualUnitRegion_logVolume :
    (paperMuLogIQCarrierActualUnitRegion places tuple μ).logVolume =
      paperMuLogHaar places tuple μ := rfl

/-- Actual paper mu_log unit-region normalization data. -/
structure PaperMuLogUnitRegionNormalization where
  unitRegion : Set (PaperIQCarrier (places := places) (tuple := tuple))
  unitRegion_eq : unitRegion = paperMuLogActualUnitRegion places tuple
  unitRegion_pos : 0 < μ unitRegion
  unitRegion_finite : μ unitRegion < ⊤
  canonicalHull_subset : arithmeticTupleCanonicalHull places tuple ⊆ unitRegion
  interface : IQHullLogVolumeInterface
    (PaperIQCarrier (places := places) (tuple := tuple))
  interface_eq : interface = paperMuLogIQCarrierActualUnitRegion places tuple μ

/-- The actual paper mu_log unit-region normalization. -/
noncomputable def paperMuLogUnitRegionNormalization :
    PaperMuLogUnitRegionNormalization places tuple μ where
  unitRegion := paperMuLogActualUnitRegion places tuple
  unitRegion_eq := rfl
  unitRegion_pos := (paperMuLogActualUnitRegion_measure_pos_lt_top places tuple μ).1
  unitRegion_finite := (paperMuLogActualUnitRegion_measure_pos_lt_top places tuple μ).2
  canonicalHull_subset := canonicalHull_subset_paperMuLogActualUnitRegion places tuple
  interface := paperMuLogIQCarrierActualUnitRegion places tuple μ
  interface_eq := rfl

end LeanFormal.IUT.XiFPaper.PaperMuLogUnitRegionActual

end
