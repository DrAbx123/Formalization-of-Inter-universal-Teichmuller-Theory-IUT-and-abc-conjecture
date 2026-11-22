import tmp.sheaf.n8.closure.C6NormalizedTensorHaar
import tmp.sheaf.n8.closure.PaperC6RegionConstructed2
import tmp.sheaf.n8.closure.C9QPilotRegion
import tmp.sheaf.n8.closure.EtaQRegionRepresentation
import tmp.sheaf.n8.closure.EtaVaryingCalibrationQOActual
import tmp.sheaf.n8.closure.C6ActualIQData

/-!
# C7 normalized region identification

Signed normalized C6 region log-volume `Rnorm` and the actual qO endpoint `Q`.
We prove the sign facts and that the minus branch `Q = -Rnorm` is impossible;
the remaining equality `Q = Rnorm` is the exact missing identification.
No arbitrary A/Z or normalization is introduced.
-/

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.C7NormalizedRegionIdentification

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaVaryingCalibrationQOActual
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open scoped BigOperators ENNReal

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type} [Fintype iota] {V : iota → Type} [∀ i, Fintype (V i)]
variable (places : (i : iota) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : iota) → V i)

/-- Actual qO endpoint Q. -/
noncomputable def qOQ (X : N8NativeInput l) : ℝ := qORegionLogVolume X

theorem qOQ_eq_qPilot (X : N8NativeInput l) : qOQ X = qPilotSignedLog X :=
  EtaVaryingCalibrationQOActual.qORegionLogVolume_eq_qPilotSignedLog X

theorem qOQ_neg (X : N8NativeInput l) : qOQ X < 0 := by
  rw [qOQ_eq_qPilot X]
  exact qPilotSignedLog_neg X

/-- Signed normalized C6 region log-volume. -/
noncomputable def normalizedRegionVolume : ℝ := by
  let T := rawData places tuple
  letI := T.measurableSpace
  exact Real.log ((c6TensorNormalizedData places tuple)
    (c6ImageSet places tuple T)).toReal

theorem normalizedRegionMass_le_one :
    (c6TensorNormalizedData places tuple)
      (c6ImageSet places tuple (rawData places tuple)) ≤ 1 := by
  let T := rawData places tuple
  letI := T.measurableSpace
  letI := T.borelSpace
  letI := T.addHaar
  have hsub : c6ImageSet places tuple T ⊆ c6UnitRegion places tuple T := by
    have himage : c6ImageSet places tuple T ⊆ c6Hull places tuple T := by
      unfold c6ImageSet c6Hull
      exact T.data.iqInterface.imageSet_subset_hull
    have hhu : c6Hull places tuple T = c6UnitRegion places tuple T := by
      unfold c6Hull c6UnitRegion
      simp [T, rawData, c6TensorActualData, C6ActualIQData.actual]
    exact himage.trans (le_of_eq hhu)
  calc
    (c6TensorNormalizedData places tuple) (c6ImageSet places tuple T)
        ≤ (c6TensorNormalizedData places tuple) (c6UnitRegion places tuple T) := by
          exact measure_mono hsub
    _ = 1 := c6TensorNormalizedData_unitRegion places tuple

theorem normalizedRegionVolume_nonpos : normalizedRegionVolume places tuple ≤ 0 := by
  have hnonneg : 0 ≤ ((c6TensorNormalizedData places tuple)
      (c6ImageSet places tuple (rawData places tuple))).toReal :=
    ENNReal.toReal_nonneg
  have hle := normalizedRegionMass_le_one places tuple
  have hleR : ((c6TensorNormalizedData places tuple)
      (c6ImageSet places tuple (rawData places tuple))).toReal ≤ 1 := by
    calc ((c6TensorNormalizedData places tuple)
        (c6ImageSet places tuple (rawData places tuple))).toReal
        ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono ENNReal.one_ne_top hle
      _ = 1 := ENNReal.toReal_one
  unfold normalizedRegionVolume
  exact Real.log_nonpos hnonneg hleR

/-- C7 normalized law: `Q` equals the normalized region volume up to sign. -/
def C7NormalizedLaw (X : N8NativeInput l)
    (places : (i : iota) → V i → FinitePlaceAtPrime K p) (tuple : (i : iota) → V i) : Prop :=
  qOQ X = normalizedRegionVolume places tuple ∨
    qOQ X = -normalizedRegionVolume places tuple

theorem minus_branch_false (X : N8NativeInput l) :
    qOQ X ≠ -normalizedRegionVolume places tuple := by
  intro h
  have hQ := qOQ_neg X
  have hR := normalizedRegionVolume_nonpos places tuple
  linarith

theorem c7NormalizedLaw_iff (X : N8NativeInput l) :
    C7NormalizedLaw X places tuple ↔ qOQ X = normalizedRegionVolume places tuple := by
  constructor
  · rintro (h | h)
    · exact h
    · exact False.elim (minus_branch_false (X := X) (places := places) (tuple := tuple) h)
  · intro h
    exact Or.inl h

/-- Exact missing identification: the actual qO endpoint equals the normalized
C6 region log-volume.  No actual production theorem bridges the qO completion
to the C6 arithmetic tensor region. -/
def MissingC7NormalizedIdentification : Prop :=
  qOQ X = normalizedRegionVolume places tuple

end LeanFormal.IUT.N8Closure.C7NormalizedRegionIdentification

end