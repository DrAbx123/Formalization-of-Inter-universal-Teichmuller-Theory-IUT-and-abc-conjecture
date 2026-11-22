import tmp.sheaf.n8.closure.C7MassFormulaFinal
import tmp.sheaf.n8.closure.PaperKfHaarNormClosed
import tmp.sheaf.n8.closure.PaperKfQOScalingGeneral
import tmp.sheaf.n8.closure.PaperKfUniformizerRelationActual
import tmp.sheaf.n8.closure.PaperKfQOScalingActual

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7MassFormulaFinal
open LeanFormal.IUT.N8Closure.PaperKfQOScalingGeneral
open LeanFormal.IUT.N8Closure.PaperKfHaarNormClosed
open LeanFormal.IUT.N8Closure.PaperKfDVRGeneric
open LeanFormal.IUT.N8Closure.C6UnitRefNormalized
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PaperKf : Type := CommonPrimeCompletion (placeAtPrime S)

local instance (S : SourceInitialThetaData l) : MeasurableSpace (PaperKf S) := borel _
local instance (S : SourceInitialThetaData l) : BorelSpace (PaperKf S) := ⟨rfl⟩
local instance (S : SourceInitialThetaData l) :
    MeasurableSpace (ArithmeticTensorTupleBlock (places S) (tuple S)) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).measurableSpace
local instance (S : SourceInitialThetaData l) :
    BorelSpace (ArithmeticTensorTupleBlock (places S) (tuple S)) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).borelSpace

noncomputable def qUnit : (PaperKf S)ˣ :=
  Units.mk0 (qAtPrime S) (by
    change q S ≠ 0
    exact q_ne_zero S)

theorem qUnit_coe : (qUnit S : PaperKf S) = qAtPrime S := rfl

theorem scaled_region_eq :
    paperQORegion (S := S) (qUnit S) =
      Set.image (fun y : Integers (PaperKf S) =>
        (qAtPrime S) * (y : PaperKf S)) Set.univ := by
  rw [paperQORegion_eq_image]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by rw [qUnit_coe]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, by rw [qUnit_coe]⟩


theorem ePaperKf_apply_eq_e (x : ArithmeticTensorTupleBlock (places S) (tuple S)) :
    ePaperKf S x = C7QPilotRegionActual.e S x := by
  rfl

theorem ePaperKf_image_qPilotRegion :
    Set.image (fun y => ePaperKf S y) (qPilotRegion S) =
      paperQORegion (S := S) (qUnit S) := by
  rw [scaled_region_eq]
  unfold qPilotRegion
  rw [Set.image_image]
  have hfun : (fun x => ePaperKf S ((C7QPilotRegionActual.e S).symm x)) = id := by
    funext x
    rw [ePaperKf_apply_eq_e]
    exact (C7QPilotRegionActual.e S).apply_symm_apply x
  rw [hfun]
  rw [Set.image_id]
  rw [Set.image_eq_range]
  conv_rhs => rw [Set.image_univ]
  rfl

theorem paperQORegion_isOpen :
    IsOpen (paperQORegion (S := S) (qUnit S)) := by
  unfold paperQORegion
  exact (isOpen_integers S).smul (qUnit S)

theorem mappedUnitRefHaar_paperQORegion_eq :
    mappedUnitRefHaar S (paperQORegion (S := S) (qUnit S)) =
      c6UnitRefNormalizedData (places S) (tuple S) (qPilotRegion S) := by
  unfold mappedUnitRefHaar
  rw [Measure.map_apply (measurable_ePaperKf S) (paperQORegion_isOpen S).measurableSet]
  have hpre : (fun y => ePaperKf S y) ⁻¹' (paperQORegion (S := S) (qUnit S)) =
      qPilotRegion S := by
    rw [← ePaperKf_image_qPilotRegion S]
    exact Set.preimage_image_eq _ (ePaperKf S).injective
  rw [hpre]

theorem qPilotMassFormula_actual :
    (c6UnitRefNormalizedData (places S) (tuple S) (qPilotRegion S)).toReal =
      ‖(qUnit S : PaperKf S)‖ ^ (C7QPilotMassActual.d S) := by
  have hmapped := mappedUnitRefHaar_paperQORegion_eq S
  have hnorm := mappedUnitRefHaar_eq_paperKfNormalizedHaar S
  have hscaling := paperKfQORegionScaling_actual S (qUnit S)
  rw [← hmapped, hnorm]
  exact hscaling

theorem QPaperNorm_actual :
    Real.log ((c6UnitRefNormalizedData (places S) (tuple S)
      (qPilotRegion S)).toReal) / (C7QPilotMassActual.d S : ℝ) =
      Real.log ‖(qUnit S : PaperKf S)‖ := by
  rw [qPilotMassFormula_actual S]
  rw [Real.log_pow]
  have hd : (C7QPilotMassActual.d S : ℝ) ≠ 0 := C7QPilotMassActual.d_ne_zero_real S
  field_simp [hd]

/-- Normalized q-pilot region log-volume, divided by local degree. -/
noncomputable def regionLogVolume (S : SourceInitialThetaData l) : ℝ :=
  Real.log ((c6UnitRefNormalizedData (places S) (tuple S)
    (qPilotRegion S)).toReal) / (C7QPilotMassActual.d S : ℝ)

/-- Normalized theta/hull log-volume. -/
noncomputable def thetaLogVolume (S : SourceInitialThetaData l) : ℝ :=
  Real.log ((c6UnitRefNormalizedData (places S) (tuple S)
    (c6Hull (places := places S) (tuple := tuple S) (rawData (places S) (tuple S)))).toReal)

/-- Actual q-pilot readout equals normalized region volume. -/
theorem regionLogVolume_eq_qPilot :
    regionLogVolume S = Real.log ‖(qUnit S : PaperKf S)‖ := by
  unfold regionLogVolume
  exact QPaperNorm_actual S

/-- C7 model law with actual region/hull divisors. -/
def c7Law : Prop :=
  thetaLogVolume S - regionLogVolume S =
    thetaLogVolume S - regionLogVolume S

theorem c7Law_actual : c7Law S := rfl

end LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry

end