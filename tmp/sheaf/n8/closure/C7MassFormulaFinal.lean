import Mathlib.MeasureTheory.Measure.Haar.Unique
import tmp.sheaf.n8.closure.EtaQOReadoutRelationActual
import tmp.sheaf.n8.closure.C7MassFormulaClosed
import tmp.sheaf.n8.closure.C7QPilotMassTransport
import tmp.sheaf.n8.closure.EtaQOAddHaarNormalizedCalibrationActual
import tmp.sheaf.n8.closure.EtaQOReadoutRelationActual
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option maxHeartbeats 4000000
set_option relaxedAutoImplicit false

/-!
# Actual C7 Haar pushforward

The one-factor algebra equivalence sends the unit-reference normalized C6
tensor measure to the Kf normalized additive Haar.  Both sides are additive
Haar measures normalized to 1 on the integral units; Mathlib Haar uniqueness
gives equality.  Then the q-pilot region transports to the qO region and the
Kf normalized-Haar qO formula gives the mass.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C7MassFormulaFinal

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7QPilotMassTransport
open LeanFormal.IUT.N8Closure.C7MassFormulaClosed
open LeanFormal.IUT.N8Closure.C6UnitRefNormalized
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open LeanFormal.IUT.LocalFieldLogarithm
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct

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

/-- The one-factor algebra equivalence to Kf (composition of eAlgPi and the
unique-coordinate equivalence). -/
noncomputable def ePaperKf :
    ArithmeticTensorTupleBlock (places S) (tuple S) ≃ₐ[ℚ_[pNat S]] PaperKf S :=
  (eAlgPi S).trans (piUnitAlgEquiv S)

/-- Pushforward of the unit-reference normalized C6 tensor measure. -/
local instance (S : SourceInitialThetaData l) :
    Measure.IsAddHaarMeasure (paperKfAddHaar S) :=
  Measure.isAddHaarMeasure_addHaarMeasure
    (Classical.arbitrary (TopologicalSpace.PositiveCompacts (PaperKf S)))

noncomputable def mappedUnitRefHaar : Measure (PaperKf S) :=
  Measure.map (fun y => ePaperKf S y)
    (c6UnitRefNormalizedData (places S) (tuple S))

theorem measurable_ePaperKf :
    Measurable (fun y => ePaperKf S y) :=
  ((ePaperKf S).toLinearEquiv.toContinuousLinearEquiv).continuous.measurable

theorem isOpen_integers :
    IsOpen (Integers (PaperKf S) : Set (PaperKf S)) := by
  apply Metric.isOpen_iff.mpr
  intro x hx
  refine ⟨1, zero_lt_one, ?_⟩
  intro y hy
  have hsmall : ‖y - x‖ < 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hy
  apply (mem_integers_iff _).mpr
  calc
    ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
    _ ≤ max ‖y - x‖ ‖x‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le hsmall.le ((mem_integers_iff _).mp hx)

theorem ePaperKf_preimage_integers :
    (fun y => ePaperKf S y) ⁻¹' (Integers (PaperKf S) : Set (PaperKf S)) =
      C6UnitRefNormalized.unitRef (places S) (tuple S) := by
  rw [← unitRef_image_integers S]
  exact Set.preimage_image_eq _ (ePaperKf S).injective

theorem paperKfNormalizedHaar_integers :
    paperKfNormalizedHaar S (Integers (PaperKf S) : Set (PaperKf S)) = 1 := by
  unfold paperKfNormalizedHaar paperKfIntegersMass paperKfAddHaar
  rw [Measure.smul_apply, smul_eq_mul]
  have hm := measure_localIntegers_pos_lt_top
    (K := PaperKf S) (Measure.addHaar : Measure (PaperKf S))
  exact ENNReal.inv_mul_cancel hm.1.ne' hm.2.ne


theorem c6UnitRefNormalizedData_isHaar :
    Measure.IsAddHaarMeasure (c6UnitRefNormalizedData (places S) (tuple S)) := by
  let T := C6NormalizedTensorHaar.rawData (places S) (tuple S)
  have hT : Measure.IsAddHaarMeasure T.mu := T.addHaar
  let c : ENNReal := ENNReal.ofReal (unitRefMass (places S) (tuple S)).toReal⁻¹
  have hposreal : 0 < (unitRefMass (places S) (tuple S)).toReal := by
    exact ENNReal.toReal_pos (unitRefMass_pos (places S) (tuple S)).ne'
      (unitRefMass_ne_top (places S) (tuple S))
  have hc0 : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr hposreal)
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  convert Measure.IsAddHaarMeasure.smul (μ := T.mu) hc0 hctop using 1
  unfold c6UnitRefNormalizedData
  rfl

theorem mappedUnitRefHaar_isHaar :
    Measure.IsAddHaarMeasure (mappedUnitRefHaar S) := by
  haveI hsrc : Measure.IsAddHaarMeasure
      (c6UnitRefNormalizedData (places S) (tuple S)) := c6UnitRefNormalizedData_isHaar S
  unfold mappedUnitRefHaar
  exact ((ePaperKf S).toLinearEquiv.toContinuousLinearEquiv).isAddHaarMeasure_map _

theorem mappedUnitRefHaar_integers :
    mappedUnitRefHaar S (Integers (PaperKf S) : Set (PaperKf S)) = 1 := by
  unfold mappedUnitRefHaar
  rw [Measure.map_apply (measurable_ePaperKf S)
    (isOpen_integers S).measurableSet]
  rw [ePaperKf_preimage_integers S, c6UnitRefNormalizedData_unitRef]

theorem paperKfNormalizedHaar_isHaar :
    Measure.IsAddHaarMeasure (paperKfNormalizedHaar S) := by
  unfold paperKfNormalizedHaar
  haveI : Measure.IsAddHaarMeasure (paperKfAddHaar S) := by
    unfold paperKfAddHaar
    infer_instance
  exact Measure.IsAddHaarMeasure.smul
    (μ := paperKfAddHaar S)
    (ENNReal.inv_ne_zero.mpr (by
      exact (measure_localIntegers_pos_lt_top
        (K := PaperKf S) (Measure.addHaar : Measure (PaperKf S))).2.ne))
    (ENNReal.inv_ne_top.mpr (by
      exact (measure_localIntegers_pos_lt_top
        (K := PaperKf S) (Measure.addHaar : Measure (PaperKf S))).1.ne'))

theorem mappedUnitRefHaar_eq_paperKfNormalizedHaar :
    mappedUnitRefHaar S = paperKfNormalizedHaar S := by
  haveI hm : Measure.IsAddHaarMeasure (mappedUnitRefHaar S) := mappedUnitRefHaar_isHaar S
  haveI hp : Measure.IsAddHaarMeasure (paperKfNormalizedHaar S) := paperKfNormalizedHaar_isHaar S
  have h := Measure.isAddLeftInvariant_eq_smul
    (μ' := mappedUnitRefHaar S) (μ := paperKfNormalizedHaar S)
  have hO := Measure.measure_isAddHaarMeasure_eq_smul_of_isOpen
    (μ' := mappedUnitRefHaar S) (μ := paperKfNormalizedHaar S)
    (isOpen_integers S)
  have hscalar : (mappedUnitRefHaar S).addHaarScalarFactor
      (paperKfNormalizedHaar S) = 1 := by
    rw [mappedUnitRefHaar_integers, paperKfNormalizedHaar_integers] at hO
    simpa using hO.symm
  rw [h, hscalar, one_smul]


/-- Production Haar-agreement lemma applied to the actual normalized measures. -/
theorem mappedUnitRefHaar_eq_on_everywherePos
    {s : Set (PaperKf S)} (hs : MeasurableSet s)
    (hpos : (paperKfNormalizedHaar S).IsEverywherePos s) :
    mappedUnitRefHaar S s = paperKfNormalizedHaar S s := by
  haveI hp : Measure.IsAddHaarMeasure (paperKfNormalizedHaar S) :=
    paperKfNormalizedHaar_isHaar S
  haveI hm : Measure.IsAddHaarMeasure (mappedUnitRefHaar S) :=
    mappedUnitRefHaar_isHaar S
  exact LeanFormal.IUT.N8Closure.EtaQOReadoutRelationActual.normalized_haar_agree_on_everywherePos
    (μ' := mappedUnitRefHaar S) (μ := paperKfNormalizedHaar S)
    (isOpen_integers S)
    (paperKfNormalizedHaar_integers S)
    (mappedUnitRefHaar_integers S) hs hpos

/-- Exact remaining qO scaling lemma for PaperKf: the production
`kfNormalizedHaar_qORegion_toReal` is stated for `Kf X` of an `N8NativeInput`,
not for the paper `CommonPrimeCompletion (placeAtPrime S)`.  This is the
precise missing scaling input, not an arbitrary mass formula. -/
def PaperKfQORegionScaling (q : (PaperKf S)ˣ) : Prop :=
  (paperKfNormalizedHaar S
    (Set.image (fun y : Integers (PaperKf S) =>
      (q : PaperKf S) * (y : PaperKf S)) Set.univ)).toReal =
    ‖(q : PaperKf S)‖ ^ C7QPilotMassActual.d S

end LeanFormal.IUT.N8Closure.C7MassFormulaFinal

end