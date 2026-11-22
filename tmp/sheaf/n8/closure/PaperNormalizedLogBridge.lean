import tmp.sheaf.n8.closure.PaperP6Final
import tmp.sheaf.n8.closure.C6ActualIQData
import tmp.sheaf.n8.closure.C6NormalizedTensorHaar
import tmp.sheaf.n8.closure.C6UnitRefNormalized
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleCanonicalHull

/-!
# Paper normalized-log bridge

Identify the normalized C6 Theta (normalized hull log-volume divided by the
local degree) with `C6ActualIQData.normalizedLogVolume` of the same actual
canonical hull.  No arbitrary normalization. -/

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperNormalizedLogBridge

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.C6UnitRefNormalized
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open LeanFormal.IUT.N8Closure.PaperP6Final
open LeanFormal.IUT.N8C6ActualIQ
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

abbrev hullSet : Set (Block S) :=
  c6Hull (places := places S) (tuple := tuple S)
    (C6NormalizedTensorHaar.rawData (places S) (tuple S))

/-- Normalized Theta: log normalized-hull mass divided by the local degree. -/
noncomputable def normalizedTheta : ℝ :=
  Real.log ((c6UnitRefNormalizedData (places S) (tuple S) (hullSet S)).toReal) /
    (Module.finrank ℚ_[pNat S] (Block S) : ℝ)

theorem normalizedTheta_eq_arithmetic :
    normalizedTheta S =
      arithmeticTupleNormalizedLogVolume (places S) (tuple S)
        (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu (hullSet S) := by
  let T := C6NormalizedTensorHaar.rawData (places S) (tuple S)
  letI := T.addHaar
  let huge : ENNReal := ENNReal.ofReal (unitRefMass (places S) (tuple S)).toReal⁻¹
  have hcoe : c6UnitRefNormalizedData (places S) (tuple S) =
      huge • T.mu := by
    unfold c6UnitRefNormalizedData huge
    rfl
  have hut_pos : 0 < (unitRefMass (places S) (tuple S)).toReal :=
    ENNReal.toReal_pos (unitRefMass_pos (places S) (tuple S)).ne'
      (unitRefMass_ne_top (places S) (tuple S))
  have hut_ne : (unitRefMass (places S) (tuple S)).toReal ≠ 0 := hut_pos.ne'
  have hraw_pos : 0 < (T.mu (hullSet S)).toReal := by
    rw [show hullSet S = arithmeticTupleCanonicalHull (places S) (tuple S) from
      PaperP6ComparisonActual.c6Hull_eq_canonicalHull S]
    exact arithmeticTupleCanonicalHull_measure_toReal_pos (places S) (tuple S) T.mu
  have hraw_ne : (T.mu (hullSet S)).toReal ≠ 0 := hraw_pos.ne'
  have hraw_fin : T.mu (hullSet S) ≠ ⊤ := by
    rw [show hullSet S = arithmeticTupleCanonicalHull (places S) (tuple S) from
      PaperP6ComparisonActual.c6Hull_eq_canonicalHull S]
    exact arithmeticTupleCanonicalHull_measure_ne_top (places S) (tuple S) T.mu
  have hout : (c6UnitRefNormalizedData (places S) (tuple S) (hullSet S)).toReal =
      (unitRefMass (places S) (tuple S)).toReal⁻¹ * (T.mu (hullSet S)).toReal := by
    rw [hcoe, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr ENNReal.toReal_nonneg)]
  have hlog : Real.log (c6UnitRefNormalizedData (places S) (tuple S) (hullSet S)).toReal =
      Real.log (T.mu (hullSet S)).toReal -
        Real.log (unitRefMass (places S) (tuple S)).toReal := by
    rw [hout, Real.log_mul (inv_ne_zero hut_ne) hraw_ne, Real.log_inv]
    ring
  have hunit : unitRefMass (places S) (tuple S) =
      T.mu (arithmeticTupleCanonicalUnitReference (places S) (tuple S)) := rfl
  rw [hunit] at hlog
  dsimp only [T] at hlog ⊢
  unfold normalizedTheta arithmeticTupleNormalizedLogVolume
  rw [hlog]
  ring_nf

theorem normalizedTheta_eq_c6NormalizedLogVolume :
    normalizedTheta S =
      (LeanFormal.IUT.N8C6ActualIQ.C6ActualIQData.actual (places S) (tuple S)
        (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu).normalizedLogVolume
        (hullSet S) := by
  letI : (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu.IsAddHaarMeasure :=
    (C6NormalizedTensorHaar.rawData (places S) (tuple S)).addHaar
  rw [normalizedTheta_eq_arithmetic]
  rfl

end LeanFormal.IUT.N8Closure.PaperNormalizedLogBridge

end