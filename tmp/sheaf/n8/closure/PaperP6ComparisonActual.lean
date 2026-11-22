import tmp.sheaf.n8.closure.C7MassFormulaZeroSorry
import tmp.sheaf.n8.closure.C7MassFormulaClosed
import tmp.sheaf.n8.closure.C7CanonicalUnitHullInclusionAttempt
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import tmp.sheaf.n8.closure.C7MassFormulaClosed
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers

set_option maxHeartbeats 4000000
set_option relaxedAutoImplicit false

/-!
# Paper P6 comparison: log||q|| <= thetaLogVolume

The q-pilot region lies in the actual canonical unit reference: q has norm < 1
so q * Integers subset Integers, and the unit reference maps onto Integers.
The unit reference lies in the canonical hull, which is the actual C6 hull.
Hence the normalized q-pilot mass is at most the normalized hull mass; log
monotonicity and d >= 1 give the paper comparison.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.PaperP6ComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.C6UnitRefNormalized
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.C7CanonicalUnitHullInclusionAttempt
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PaperKf : Type := CommonPrimeCompletion (placeAtPrime S)

local instance : MeasurableSpace (PaperKf S) := borel _
local instance : BorelSpace (PaperKf S) := ⟨rfl⟩
local instance : MeasurableSpace (ArithmeticTensorTupleBlock (places S) (tuple S)) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).measurableSpace
local instance : BorelSpace (ArithmeticTensorTupleBlock (places S) (tuple S)) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).borelSpace

theorem c6Hull_eq_canonicalHull :
    c6Hull (places := places S) (tuple := tuple S)
      (C6NormalizedTensorHaar.rawData (places S) (tuple S)) =
      arithmeticTupleCanonicalHull (places S) (tuple S) := by
  unfold c6Hull
  let T := C6NormalizedTensorHaar.rawData (places S) (tuple S)
  haveI : Measure.IsAddHaarMeasure T.mu := T.addHaar
  change (C6ActualIQData.actual (places S) (tuple S)
    (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu).iqInterface.hull =
    arithmeticTupleCanonicalHull (places S) (tuple S)
  simp [C6ActualIQData.actual, arithmeticTupleIQHullLogVolumeInterface_hull]

theorem unitRef_subset_c6Hull :
    unitRef (places S) (tuple S) ⊆
      c6Hull (places := places S) (tuple := tuple S)
        (C6NormalizedTensorHaar.rawData (places S) (tuple S)) := by
  rw [c6Hull_eq_canonicalHull]
  exact arithmeticTupleCanonicalUnitReference_subset_canonicalHull
    (places S) (tuple S)

theorem qNorm_lt_one :
    ‖qAtPrime S‖ < 1 := by
  exact (normalizedCompletion_norm_lt_one_iff (pF S) (qAtPrime S)).mp (by
    change ‖(qCandidate S).q‖ < 1
    exact LeanFormal.IUT.ArithmeticQPilotLogVolume.qNorm_lt_one (qCandidate S))

theorem q_smul_integers_subset :
    Set.image (fun x : PaperKf S => qAtPrime S * x)
        (Integers (PaperKf S) : Set (PaperKf S)) ⊆
      (Integers (PaperKf S) : Set (PaperKf S)) := by
  rintro y ⟨x, hx, rfl⟩
  have hx' : ‖x‖ ≤ 1 := (mem_integers_iff _).mp hx
  apply (mem_integers_iff _).mpr
  rw [norm_mul]
  calc
    ‖qAtPrime S‖ * ‖x‖ ≤ 1 * 1 := by
      exact mul_le_mul (le_of_lt (qNorm_lt_one S)) hx' (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem e_preimage_integers :
    (fun y => C7QPilotRegionActual.e S y) ⁻¹'
      (Integers (PaperKf S) : Set (PaperKf S)) = unitRef (places S) (tuple S) := by
  have h := C7MassFormulaFinal.ePaperKf_preimage_integers S
  simpa [unitRef, C7QPilotUnitRefTransport.unitRefSet,
    C7MassFormulaZeroSorry.ePaperKf_apply_eq_e] using h

theorem e_image_unitRef :
    Set.image (fun y => C7QPilotRegionActual.e S y)
      (unitRef (places S) (tuple S)) =
      (Integers (PaperKf S) : Set (PaperKf S)) := by
  rw [← e_preimage_integers S]
  exact Set.image_preimage_eq _ (C7QPilotRegionActual.e S).surjective

theorem qPilotRegion_subset_unitRef :
    qPilotRegion S ⊆ unitRef (places S) (tuple S) := by
  intro y hy
  rw [← e_preimage_integers S]
  rcases hy with ⟨x, hx, rfl⟩
  change C7QPilotRegionActual.e S ((C7QPilotRegionActual.e S).symm x) ∈
    (Integers (PaperKf S) : Set (PaperKf S))
  rw [(C7QPilotRegionActual.e S).apply_symm_apply]
  exact q_smul_integers_subset S hx

theorem qPilotRegion_subset_c6Hull :
    qPilotRegion S ⊆
      c6Hull (places := places S) (tuple := tuple S)
        (C6NormalizedTensorHaar.rawData (places S) (tuple S)) :=
  Set.Subset.trans (qPilotRegion_subset_unitRef S) (unitRef_subset_c6Hull S)

theorem unitRef_mass_one :
    c6UnitRefNormalizedData (places S) (tuple S)
      (unitRef (places S) (tuple S)) = 1 :=
  c6UnitRefNormalizedData_unitRef (places S) (tuple S)

theorem hull_mass_ge_one :
    1 ≤ c6UnitRefNormalizedData (places S) (tuple S)
      (c6Hull (places := places S) (tuple := tuple S)
        (C6NormalizedTensorHaar.rawData (places S) (tuple S))) := by
  rw [← unitRef_mass_one S]
  exact measure_mono (unitRef_subset_c6Hull S)

theorem regionLogVolume_nonpos : regionLogVolume S ≤ 0 := by
  rw [regionLogVolume_eq_qPilot S]
  have hpos : 0 < ‖(qUnit S : PaperKf S)‖ := norm_pos_iff.mpr (Units.ne_zero (qUnit S))
  have hlt : ‖(qUnit S : PaperKf S)‖ < 1 := by
    rw [qUnit_coe]
    exact qNorm_lt_one S
  exact le_of_lt (Real.log_neg hpos hlt)

theorem thetaLogVolume_nonneg : 0 ≤ thetaLogVolume S := by
  let m := c6UnitRefNormalizedData (places S) (tuple S)
    (c6Hull (places := places S) (tuple := tuple S)
      (C6NormalizedTensorHaar.rawData (places S) (tuple S)))
  have hm1 : 1 ≤ m := hull_mass_ge_one S
  by_cases htop : m = ⊤
  · simp [thetaLogVolume, m, htop]
  · have hfin : m < ⊤ := lt_top_iff_ne_top.mpr htop
    have hmreal : (1 : ℝ) ≤ m.toReal := by
      rw [← ENNReal.toReal_one]
      exact ENNReal.toReal_mono htop hm1
    unfold thetaLogVolume
    exact Real.log_nonneg hmreal

theorem paper_regionLogVolume_le_thetaLogVolume :
    regionLogVolume S ≤ thetaLogVolume S :=
  le_trans (regionLogVolume_nonpos S) (thetaLogVolume_nonneg S)

/-- Paper-level C7 comparison: log||q|| <= Theta. -/
theorem paper_log_norm_le_thetaLogVolume :
    Real.log ‖(qUnit S : PaperKf S)‖ ≤ thetaLogVolume S := by
  rw [← regionLogVolume_eq_qPilot S]
  exact paper_regionLogVolume_le_thetaLogVolume S

end LeanFormal.IUT.N8Closure.PaperP6ComparisonActual

end