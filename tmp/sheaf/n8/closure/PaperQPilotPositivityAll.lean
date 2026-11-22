import tmp.sheaf.n8.closure.PaperAllQPilotRegions
import tmp.sheaf.n8.closure.PaperKfQOScalingActual
import tmp.sheaf.n8.closure.C7MassFormulaFinal
import tmp.sheaf.n8.closure.C6UnitRefNormalized

noncomputable section
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 8000000

namespace LeanFormal.IUT.N8Closure.PaperQPilotPositivityAll

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7MassFormulaZeroSorry
open LeanFormal.IUT.N8Closure.PaperAllQPilotRegions
open LeanFormal.IUT.N8Closure.C7MassFormulaFinal
open LeanFormal.IUT.N8Closure.PaperKfQOScalingGeneral
open LeanFormal.IUT.N8Closure.C6UnitRefNormalized
open LeanFormal.IUT.N8Closure.C7QPilotMassTransport
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev Block (S : SourceInitialThetaData l) : Type :=
  ArithmeticTensorTupleBlock (places S) (tuple S)

local instance : MeasurableSpace (Block S) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).measurableSpace
local instance : BorelSpace (Block S) :=
  (C6NormalizedTensorHaar.rawData (places S) (tuple S)).borelSpace
local instance : MeasurableSpace (C7MassFormulaZeroSorry.PaperKf S) := borel _
local instance : BorelSpace (C7MassFormulaZeroSorry.PaperKf S) := ⟨rfl⟩
local instance : MeasurableSpace (C7MassFormulaFinal.PaperKf S) := borel _
local instance : BorelSpace (C7MassFormulaFinal.PaperKf S) := ⟨rfl⟩
local instance : MeasurableSpace (PaperKfQOScalingGeneral.PaperKf S) := borel _
local instance : BorelSpace (PaperKfQOScalingGeneral.PaperKf S) := ⟨rfl⟩

theorem qPilotRegionOf_eq_preimage (q : (C7MassFormulaZeroSorry.PaperKf S)ˣ) :
    qPilotRegionOf S q =
      (fun x : Block S => C7MassFormulaFinal.ePaperKf S x) ⁻¹' (paperQORegion S q) := by
  have hfun : (fun x : Block S => C7MassFormulaFinal.ePaperKf S x) =
      (fun x : Block S => C7QPilotRegionActual.e S x) := by
    funext x
    exact C7MassFormulaZeroSorry.ePaperKf_apply_eq_e S x
  rw [hfun]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change C7QPilotRegionActual.e S ((C7QPilotRegionActual.e S).symm y) ∈ paperQORegion S q
    rw [(C7QPilotRegionActual.e S).apply_symm_apply]
    exact hy
  · intro hx
    exact ⟨C7QPilotRegionActual.e S x, hx, (C7QPilotRegionActual.e S).symm_apply_apply x⟩

theorem paperQORegion_isOpen_of (q : (C7MassFormulaZeroSorry.PaperKf S)ˣ) :
    IsOpen (paperQORegion S q) := by
  unfold paperQORegion
  exact (isOpen_integers S).smul q

theorem normalized_mass_qPilotRegion_eq_paperKf (q : (C7MassFormulaZeroSorry.PaperKf S)ˣ) :
    c6UnitRefNormalizedData (places S) (tuple S) (qPilotRegionOf S q) =
      C7QPilotMassTransport.paperKfNormalizedHaar S (paperQORegion S q) := by
  rw [qPilotRegionOf_eq_preimage S q]
  rw [← C7MassFormulaFinal.mappedUnitRefHaar_eq_paperKfNormalizedHaar S]
  unfold C7MassFormulaFinal.mappedUnitRefHaar
  exact (Measure.map_apply
    (μ := c6UnitRefNormalizedData (places S) (tuple S))
    (C7MassFormulaFinal.measurable_ePaperKf S)
    (paperQORegion_isOpen_of S q).measurableSet).symm

theorem normalized_mass_qPilotRegion_pos (q : (C7MassFormulaZeroSorry.PaperKf S)ˣ) :
    0 < c6UnitRefNormalizedData (places S) (tuple S) (qPilotRegionOf S q) := by
  rw [normalized_mass_qPilotRegion_eq_paperKf S q]
  have h := paperKfQORegionScaling_actual S q
  have hpos : 0 < (C7QPilotMassTransport.paperKfNormalizedHaar S (paperQORegion S q)).toReal := by
    rw [h]
    exact pow_pos (norm_pos_iff.mpr (Units.ne_zero q)) _
  have hne : C7QPilotMassTransport.paperKfNormalizedHaar S (paperQORegion S q) ≠ 0 := by
    intro hz
    rw [hz, ENNReal.toReal_zero] at hpos
    exact lt_irrefl _ hpos
  exact pos_iff_ne_zero.mpr hne

theorem raw_mass_pos_of_mem_allQPilotRegions
    {T : Set (Block S)} (hT : T ∈ allQPilotRegions S) :
    0 < (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu T := by
  rcases hT with ⟨q, _hq, rfl⟩
  have hnormpos := normalized_mass_qPilotRegion_pos S q
  by_contra hraw
  have hraw0 : (C6NormalizedTensorHaar.rawData (places S) (tuple S)).mu
      (qPilotRegionOf S q) = 0 := by
    apply le_antisymm
    · exact le_of_not_gt hraw
    · exact bot_le
  unfold c6UnitRefNormalizedData at hnormpos
  rw [Measure.smul_apply, smul_eq_mul, hraw0, mul_zero] at hnormpos
  exact lt_irrefl _ hnormpos

end LeanFormal.IUT.N8Closure.PaperQPilotPositivityAll

end