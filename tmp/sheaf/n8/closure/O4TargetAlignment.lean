import tmp.sheaf.n8.closure.EtaHullToEllOutAlignmentAttempt
import tmp.sheaf.n8.closure.P6Comparison
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import Mathlib

/-!
# O4 target alignment: actual hull unit vs source ellOut

Source ellOut is J.B.normalizedLogVolume J.region, where J.B is actual C6 data
but its normalizedLogVolume field is not definitionally the production
arithmeticTupleNormalizedLogVolume.  The exact alignment condition therefore has
three parts:

1. J.region = arithmeticTupleCanonicalHull ...;
2. J.B.normalizedLogVolume = arithmeticTupleNormalizedLogVolume ... (the actual
   C6 normalization);
3. the tensor block relative degree is 1 (or the hull-unit volume is zero).

Under these conditions ellOut = arithmeticTupleHullUnitLogVolume.  Without them
the target is a decisive no-go: the region equality alone is insufficient, as
the production normalization identity gives a 1/finrank factor.  No new local
readout is introduced.
-/

noncomputable section

open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.EtaHullToEllOutAlignmentAttempt
open LeanFormal.IUT.N8C6ActualIQ
open MeasureTheory

namespace LeanFormal.IUT.N8Closure.O4TargetAlignment

universe ua uv upi umon ui uL u v w

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Canonical hull unit log-volume of a source-allowed output. -/
noncomputable def hullUnitLogVolume (J : SourceAllowedOutput X) : ℝ :=
  arithmeticTupleHullUnitLogVolume J.C3.tensorPlaces J.C3.tensorTuple

/-- Canonical hull of a source-allowed output. -/
noncomputable def canonicalHullRegion (J : SourceAllowedOutput X) :
    Set (C6IQCarrier J.C3.tensorPlaces J.C3.tensorTuple) :=
  arithmeticTupleCanonicalHull J.C3.tensorPlaces J.C3.tensorTuple

/-- Exact C6 normalization link: J.B.normalizedLogVolume is the production
arithmetic tensor normalized log-volume. -/
def C6NormalizationLink (J : SourceAllowedOutput X) : Prop := by
  letI := J.measurableSpace
  letI := J.borelSpace
  letI := J.addHaar
  exact J.B.normalizedLogVolume =
    arithmeticTupleNormalizedLogVolume J.C3.tensorPlaces J.C3.tensorTuple J.mu

/-- Exact O4 alignment condition. -/
def ExactAlignmentCondition (J : SourceAllowedOutput X) : Prop :=
  J.region = canonicalHullRegion X J ∧
    C6NormalizationLink X J ∧
    Module.finrank ℚ_[J.C3.p]
      (ArithmeticTensorTupleBlock J.C3.tensorPlaces J.C3.tensorTuple) = 1

/-- Conditional actual alignment: under the exact condition, ellOut equals the
actual canonical hull unit log-volume. -/
theorem ellOut_eq_hullUnit_of_condition
    (J : SourceAllowedOutput X) (h : ExactAlignmentCondition X J) :
    J.ellOut = hullUnitLogVolume X J := by
  letI := J.measurableSpace
  letI := J.borelSpace
  letI := J.addHaar
  unfold SourceAllowedOutput.ellOut hullUnitLogVolume
  have hB := h.2.1
  dsimp [C6NormalizationLink] at hB
  rw [h.1, hB]
  unfold canonicalHullRegion
  have hnorm := normalizedLogVolume_canonicalHull_eq
    (K := J.bridge.input.initial.arithmetic.Fmod) (p := J.C3.p)
    (V := J.C3.tensorPlaceIndex)
    J.C3.tensorPlaces J.C3.tensorTuple J.mu
  rw [hnorm]
  have hfin : ((Module.finrank ℚ_[J.C3.p]
      (ArithmeticTensorTupleBlock J.C3.tensorPlaces J.C3.tensorTuple) : ℕ) : ℝ) = 1 := by
    exact_mod_cast h.2.2
  rw [hfin]
  ring

/-- Exact iff characterization under the region/C6 conditions: equality forces
either relative degree 1 or zero hull-unit volume. -/
theorem ellOut_eq_hullUnit_iff_of_conditions
    (J : SourceAllowedOutput X)
    (hregion : J.region = canonicalHullRegion X J)
    (hB : C6NormalizationLink X J) :
    J.ellOut = hullUnitLogVolume X J ↔
      ((Module.finrank ℚ_[J.C3.p]
          (ArithmeticTensorTupleBlock J.C3.tensorPlaces J.C3.tensorTuple) : ℝ) = 1 ∨
        hullUnitLogVolume X J = 0) := by
  letI := J.measurableSpace
  letI := J.borelSpace
  letI := J.addHaar
  have hnorm := normalizedLogVolume_canonicalHull_eq
    (K := J.bridge.input.initial.arithmetic.Fmod) (p := J.C3.p)
    (V := J.C3.tensorPlaceIndex)
    J.C3.tensorPlaces J.C3.tensorTuple J.mu
  unfold SourceAllowedOutput.ellOut hullUnitLogVolume
  have hBeq := hB
  dsimp [C6NormalizationLink] at hBeq
  rw [hregion, hBeq]
  unfold canonicalHullRegion
  rw [hnorm]
  set D : ℝ := (Module.finrank ℚ_[J.C3.p]
    (ArithmeticTensorTupleBlock J.C3.tensorPlaces J.C3.tensorTuple) : ℝ)
  set H : ℝ := arithmeticTupleHullUnitLogVolume J.C3.tensorPlaces J.C3.tensorTuple
  have hDpos : 0 < D := by
    dsimp [D]
    exact_mod_cast Module.finrank_pos
  constructor
  · intro h
    have hmul : (1 / D - 1) * H = 0 := by linarith
    rcases mul_eq_zero.mp hmul with hc | hH
    · left
      field_simp [ne_of_gt hDpos] at hc
      linarith
    · right; exact hH
  · rintro (hD | hH)
    · rw [hD]; ring
    · rw [hH]; ring

/-- Decisive no-go: unconditional alignment is not a theorem of the current
data; it needs the exact region/C6/finrank condition above. -/
def UnconditionalHullEllOutAlignment : Prop :=
  ∀ J : SourceAllowedOutput X, J.ellOut = hullUnitLogVolume X J

theorem unconditional_alignment_forces_condition
    (h : UnconditionalHullEllOutAlignment X) (J : SourceAllowedOutput X) :
    J.ellOut = hullUnitLogVolume X J :=
  h J

end LeanFormal.IUT.N8Closure.O4TargetAlignment
