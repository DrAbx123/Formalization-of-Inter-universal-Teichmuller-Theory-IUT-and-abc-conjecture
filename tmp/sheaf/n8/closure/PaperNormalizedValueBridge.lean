import tmp.sheaf.n8.closure.PaperNormalizedLogBridge
import tmp.sheaf.n8.closure.PaperP6NormalizedValuesActual
import tmp.sheaf.n8.closure.PaperAllQPilotRegions
import tmp.sheaf.n8.closure.PaperP6Final

/-!
# Normalized value bridge

For any region T with positive finite raw Haar mass, the normalized actual
value equals `C6ActualIQData.normalizedLogVolume T`. -/

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperNormalizedValueBridge

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.C6UnitRefNormalized
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open LeanFormal.IUT.N8Closure.PaperAllQPilotRegions
open LeanFormal.IUT.N8Closure.PaperP6Final
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev Block : Type := ArithmeticTensorTupleBlock (places S) (tuple S)

local instance : MeasurableSpace (Block S) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).measurableSpace
local instance : BorelSpace (Block S) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).borelSpace
local instance rawAddHaar :
    (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu.IsAddHaarMeasure :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).addHaar

noncomputable def normalizedValue (T : Set (Block S)) : ℝ :=
  Real.log ((c6UnitRefNormalizedData (places S) (tuple S) T).toReal) /
    (Module.finrank ℚ_[pNat S] (Block S) : ℝ)

theorem normalizedValue_eq_c6 (T : Set (Block S))
    (hpos : 0 < (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu T)
    (hfin : (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu T < ⊤) :
    normalizedValue S T =
      (LeanFormal.IUT.N8C6ActualIQ.C6ActualIQData.actual (places S) (tuple S)
        (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu).normalizedLogVolume T := by
  let R := C6NormalizedTensorHaar.rawData (places S) (tuple S)
  letI := R.addHaar
  let huge : ENNReal := ENNReal.ofReal (unitRefMass (places S) (tuple S)).toReal⁻¹
  have hcoe : c6UnitRefNormalizedData (places S) (tuple S) = huge • R.mu := by
    unfold c6UnitRefNormalizedData huge
    rfl
  have hut_pos : 0 < (unitRefMass (places S) (tuple S)).toReal :=
    ENNReal.toReal_pos (unitRefMass_pos (places S) (tuple S)).ne'
      (unitRefMass_ne_top (places S) (tuple S))
  have hut_ne : (unitRefMass (places S) (tuple S)).toReal ≠ 0 := hut_pos.ne'
  have hTpos : 0 < (R.mu T).toReal :=
    ENNReal.toReal_pos hpos.ne' (ne_of_lt hfin)
  have hTne : (R.mu T).toReal ≠ 0 := hTpos.ne'
  have hout : (c6UnitRefNormalizedData (places S) (tuple S) T).toReal =
      (unitRefMass (places S) (tuple S)).toReal⁻¹ * (R.mu T).toReal := by
    rw [hcoe, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr ENNReal.toReal_nonneg)]
  have hlog : Real.log (c6UnitRefNormalizedData (places S) (tuple S) T).toReal =
      Real.log (R.mu T).toReal -
        Real.log (unitRefMass (places S) (tuple S)).toReal := by
    rw [hout, Real.log_mul (inv_ne_zero hut_ne) hTne, Real.log_inv]
    ring
  have hunit : unitRefMass (places S) (tuple S) =
      R.mu (arithmeticTupleCanonicalUnitReference (places S) (tuple S)) := rfl
  rw [hunit] at hlog
  dsimp only [R] at hlog ⊢
  rw [show (LeanFormal.IUT.N8C6ActualIQ.C6ActualIQData.actual (places S) (tuple S)
      (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu).normalizedLogVolume T =
      arithmeticTupleNormalizedLogVolume (places S) (tuple S)
        (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu T from rfl]
  unfold normalizedValue arithmeticTupleNormalizedLogVolume
  rw [hlog]
  ring_nf


/-- Actual degree-normalized paper value set from all q-pilot regions. -/
def normalizedValueSet : Set ℝ :=
  {z | ∃ T ∈ allQPilotRegions S, z = normalizedValue S T}

theorem raw_mass_lt_top_of_mem_allQPilotRegions
    {T : Set (Block S)} (hT : T ∈ allQPilotRegions S) :
    (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu T < ⊤ := by
  let R := C6NormalizedTensorHaar.rawData (places S) (tuple S)
  have hsub : T ⊆ c6Hull (places := places S) (tuple := tuple S) R :=
    allQPilotRegions_subset_hull S T hT
  have hraw : R.mu (c6Hull (places := places S) (tuple := tuple S) R) < ⊤ := by
    rw [PaperP6ComparisonActual.c6Hull_eq_canonicalHull S]
    exact (measure_arithmeticTupleCanonicalRegions_pos_lt_top (places S) (tuple S) R.mu).1.2
  exact lt_of_le_of_lt (measure_mono hsub) hraw

/-- Every value in `normalizedValueSet`, under the actual positivity condition for
all q-pilot regions, equals the corresponding C6 `normalizedLogVolume`. -/
theorem normalizedValueSet_eq_c6NormalizedLogVolume
    (hpos : ∀ T ∈ allQPilotRegions S,
      0 < (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu T) :
    ∀ z ∈ normalizedValueSet S,
      ∃ T ∈ allQPilotRegions S,
        z = (LeanFormal.IUT.N8C6ActualIQ.C6ActualIQData.actual (places S) (tuple S)
          (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu).normalizedLogVolume T := by
  rintro z ⟨T, hT, rfl⟩
  exact ⟨T, hT, normalizedValue_eq_c6 S T (hpos T hT)
    (raw_mass_lt_top_of_mem_allQPilotRegions S hT)⟩



end LeanFormal.IUT.N8Closure.PaperNormalizedValueBridge

end