import tmp.sheaf.n8.closure.EtaValueGroupLineActual

/-!
# EtaQRegionRepresentation

ETA v2: actual non-singleton representation of the native qO region.

The old `qPilotRegionSource` is the singleton `{q}`.  The actual qO region is
the honest `q * O` region in the native q completion:

  qORegion X := { q * y | y ∈ O },

where `O = Integers (Completion (nativeFPlaceOverBad X))` is the production
integral unit ball.  It contains both `q` and `0`; since `q ≠ 0` it is not a
singleton.

Calibration: its log norm is exactly the production q-pilot Kummer-relative
log volume (`qPilotKummerRelativeVolume`).  The additive Haar scaling identity
for this region is the exact remaining source/measure gap; no raw q scalar is
used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaQRegionRepresentation

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped NumberField

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Native q completion carrier. -/
abbrev QCompletion : Type := Completion (nativeFPlaceOverBad X)

noncomputable instance qCompletionMeasurableSpace : MeasurableSpace (QCompletion X) :=
  borel (QCompletion X)

instance qCompletionBorelSpace : BorelSpace (QCompletion X) := ⟨rfl⟩

/-- Actual qO region: the q-multiple of the production integral unit ball. -/
def qORegion : Set (QCompletion X) :=
  {x | ∃ y : Integers (QCompletion X), x = (C9QPilotRegion.nativeQ X).q * (y : QCompletion X)}

theorem q_mem_qORegion : (C9QPilotRegion.nativeQ X).q ∈ qORegion X :=
  ⟨1, by simp⟩

theorem zero_mem_qORegion : (0 : QCompletion X) ∈ qORegion X :=
  ⟨0, by simp⟩

/-- The qO region is not a singleton. -/
theorem qORegion_nontrivial :
    ∃ x ∈ qORegion X, ∃ y ∈ qORegion X, x ≠ y :=
  ⟨(C9QPilotRegion.nativeQ X).q, q_mem_qORegion X,
    0, zero_mem_qORegion X, (C9QPilotRegion.nativeQ X).q_ne_zero⟩

/-- Actual log-norm calibration of the qO region. -/
def qORegionLogVolume : ℝ :=
  Real.log ‖(C9QPilotRegion.nativeQ X).q‖

theorem qORegionLogVolume_eq_qPilotKummer :
    qORegionLogVolume X = qPilotKummerRelativeVolume X := by
  simp [qORegionLogVolume, qPilotKummerRelativeVolume, unitNormLogDegree]

/-- Exact Haar calibration target for the actual qO region: the additive Haar
measure of `qO` is the norm factor times the measure of `O`. -/
def EtaQRegionHaarCalibration
    (μ : MeasureTheory.Measure (QCompletion X))
    [MeasureTheory.Measure.IsAddHaarMeasure μ] : Prop :=
  μ (qORegion X) =
    ENNReal.ofReal (Real.exp (qORegionLogVolume X)) *
      μ (Integers (QCompletion X) : Set (QCompletion X))

/-- Packet diagonal representation: currently the selected-place packet is the
one native bad place, so the diagonal qO region is the actual qO region; a
multi-place diagonal remains the exact packet gap. -/
def qOPacketDiagonalRegion : Set (QCompletion X) :=
  qORegion X

/-- The native selected-place packet is the singleton at the bad F-place. -/
theorem qPilotSelectedPlaces_singleton :
    qPilotSelectedPlaces X = {nativeFPlaceOverBad X} := rfl

theorem qOPacketDiagonalRegion_eq :
    qOPacketDiagonalRegion X = qORegion X := rfl

end LeanFormal.IUT.N8Closure.EtaQRegionRepresentation