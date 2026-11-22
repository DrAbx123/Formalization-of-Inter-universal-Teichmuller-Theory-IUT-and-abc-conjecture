import tmp.sheaf.n8.closure.C6TensorActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullSignedLogVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull

/-!
# Normalized C6 tensor Haar

Scale the actual raw C6 tensor Haar by the inverse mass of the actual IQ unit
region, prove normalized unit mass one, and define normalized tensor Theta and
region log-volumes.
-/

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8C6ActualIQ
open MeasureTheory
open scoped BigOperators ENNReal

variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type} [Fintype iota] {V : iota → Type} [∀ i, Fintype (V i)]
variable (places : (i : iota) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : iota) → V i)


abbrev Block (places : (i : iota) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : iota) → V i) : Type := ArithmeticTensorTupleBlock places tuple

noncomputable def rawData : C6TensorActualData places tuple :=
  c6TensorActualData places tuple

noncomputable def c6UnitRegion (T : C6TensorActualData places tuple) :
    Set (Block places tuple) := by
  letI := T.measurableSpace
  letI := T.borelSpace
  letI := T.addHaar
  exact T.data.iqInterface.unitRegion

noncomputable def c6Hull (T : C6TensorActualData places tuple) :
    Set (Block places tuple) := by
  letI := T.measurableSpace
  letI := T.borelSpace
  letI := T.addHaar
  exact T.data.iqInterface.hull

noncomputable def c6ImageSet (T : C6TensorActualData places tuple) :
    Set (Block places tuple) := by
  letI := T.measurableSpace
  letI := T.borelSpace
  letI := T.addHaar
  exact T.data.iqInterface.imageSet

theorem actual_unitRegion_eq_canonical :
    c6UnitRegion places tuple (rawData places tuple) =
      arithmeticTupleCanonicalHull places tuple := by
  unfold c6UnitRegion
  let T := rawData places tuple
  letI := T.measurableSpace
  letI := T.borelSpace
  letI := T.addHaar
  simp [T, rawData, c6TensorActualData, C6ActualIQData.actual]

theorem actual_unitRegion_mass_pos :
    0 < ((rawData places tuple).mu
      (c6UnitRegion places tuple (rawData places tuple))).toReal := by
  let T := rawData places tuple
  letI := T.measurableSpace
  letI := T.borelSpace
  letI := T.addHaar
  rw [actual_unitRegion_eq_canonical places tuple]
  exact arithmeticTupleCanonicalHull_measure_toReal_pos places tuple T.mu

theorem actual_unitRegion_mass_ne_top :
    (rawData places tuple).mu
      (c6UnitRegion places tuple (rawData places tuple)) ≠ ⊤ := by
  let T := rawData places tuple
  letI := T.measurableSpace
  letI := T.borelSpace
  letI := T.addHaar
  rw [actual_unitRegion_eq_canonical places tuple]
  exact arithmeticTupleCanonicalHull_measure_ne_top places tuple T.mu

/-- Normalized measure from raw tensor C6 data, scaled by inverse unit mass. -/
noncomputable def c6TensorNormalizedMeasure (T : C6TensorActualData places tuple)
    (hpos : 0 < (T.mu (c6UnitRegion places tuple T)).toReal) :
    @Measure (Block places tuple) T.measurableSpace := by
  letI := T.measurableSpace
  letI := T.borelSpace
  letI := T.addHaar
  exact ENNReal.ofReal ((T.mu (c6UnitRegion places tuple T)).toReal)⁻¹ • T.mu

/-- Actual normalized C6 tensor Haar. -/
noncomputable def c6TensorNormalizedData :
    @Measure (Block places tuple) (rawData places tuple).measurableSpace :=
  c6TensorNormalizedMeasure places tuple (rawData places tuple)
    (actual_unitRegion_mass_pos places tuple)

theorem c6TensorNormalizedData_unitRegion :
    c6TensorNormalizedData places tuple
      (c6UnitRegion places tuple (rawData places tuple)) = 1 := by
  let T := rawData places tuple
  letI := T.measurableSpace
  letI := T.borelSpace
  letI := T.addHaar
  have hfin : T.mu (c6UnitRegion places tuple T) ≠ ⊤ :=
    actual_unitRegion_mass_ne_top places tuple
  set m : ℝ := (T.mu (c6UnitRegion places tuple T)).toReal with hm
  have hμeq : T.mu (c6UnitRegion places tuple T) = ENNReal.ofReal m := by
    rw [hm, ENNReal.ofReal_toReal]
    exact hfin
  have hmpos : 0 < m := by
    rw [hm]
    exact actual_unitRegion_mass_pos places tuple
  have hmne : m ≠ 0 := hmpos.ne'
  have hmto : (ENNReal.ofReal m).toReal = m :=
    ENNReal.toReal_ofReal (le_of_lt hmpos)
  unfold c6TensorNormalizedData c6TensorNormalizedMeasure
  rw [Measure.smul_apply, smul_eq_mul]
  rw [hμeq, hmto]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ENNReal.toReal_nonneg)]
  rw [inv_mul_cancel₀ hmne, ENNReal.ofReal_one]

noncomputable def c6NormalizedTheta : ENNReal := by
  let T := rawData places tuple
  letI := T.measurableSpace
  letI := T.borelSpace
  letI := T.addHaar
  exact haarLogVolume (c6TensorNormalizedData places tuple) (c6Hull places tuple T)

noncomputable def c6NormalizedRegionVolume : ENNReal := by
  let T := rawData places tuple
  letI := T.measurableSpace
  letI := T.borelSpace
  letI := T.addHaar
  exact haarLogVolume (c6TensorNormalizedData places tuple) (c6ImageSet places tuple T)

theorem c6NormalizedRegionVolume_le_theta :
    c6NormalizedRegionVolume places tuple ≤ c6NormalizedTheta places tuple := by
  let T := rawData places tuple
  letI := T.measurableSpace
  letI := T.borelSpace
  letI := T.addHaar
  unfold c6NormalizedRegionVolume c6NormalizedTheta
  dsimp only
  have hsub : c6ImageSet places tuple T ⊆ c6Hull places tuple T := by
    unfold c6ImageSet c6Hull
    exact T.data.iqInterface.imageSet_subset_hull
  exact haarLogVolume_mono (μ := c6TensorNormalizedData places tuple)
    (S := c6ImageSet places tuple T) (T := c6Hull places tuple T) hsub

end LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar

end