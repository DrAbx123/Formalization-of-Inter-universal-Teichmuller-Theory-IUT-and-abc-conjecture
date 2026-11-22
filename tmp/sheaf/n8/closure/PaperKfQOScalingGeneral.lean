import tmp.sheaf.n8.closure.C7MassFormulaFinal
import tmp.sheaf.n8.closure.EtaQHaarScalingCalibration
import tmp.sheaf.n8.closure.EtaHaarCharNormIdentification

set_option maxHeartbeats 4000000
set_option relaxedAutoImplicit false

/-!
# PaperKf qO Haar scaling, general local-field context

Reduce the paper `PaperKfQORegionScaling` to the single generic local-field
lemma `HararNormIdentificationTarget`: mK(q) = ||q||^d.  The actual qO region
is q times the integral unit ball, and `measure_units_smul` gives the scaling.
The remaining generic norm identification is recorded as the exact gap; no
native `N8NativeInput` and no arbitrary scaling formula are used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.PaperKfQOScalingGeneral

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.N8Closure.C7QPilotRegionActual
open LeanFormal.IUT.N8Closure.C7QPilotMassTransport
open LeanFormal.IUT.N8Closure.C7MassFormulaFinal
open LeanFormal.IUT.N8Closure.EtaQHaarScalingCalibration
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.N8Closure.EtaHaarCharNormIdentification
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct Pointwise

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

abbrev PaperKf : Type := CommonPrimeCompletion (placeAtPrime S)

local instance : MeasurableSpace (PaperKf S) := borel _
local instance : BorelSpace (PaperKf S) := ⟨rfl⟩

/-- q times the integral unit ball, on the paper completion. -/
noncomputable def paperQORegion (q : (PaperKf S)ˣ) : Set (PaperKf S) :=
  q • (Integers (PaperKf S) : Set (PaperKf S))

theorem paperQORegion_eq_image (q : (PaperKf S)ˣ) :
    paperQORegion S q =
      Set.image (fun y : Integers (PaperKf S) =>
        (q : PaperKf S) * (y : PaperKf S)) Set.univ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, Set.mem_univ _, by simp [Units.smul_def]⟩
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, y.property, by simp [Units.smul_def]⟩

/-- The qO scaling target for the paper completion. -/
def PaperKfQORegionScaling (q : (PaperKf S)ˣ) : Prop :=
  (paperKfNormalizedHaar S (paperQORegion S q)).toReal =
    ‖(q : PaperKf S)‖ ^ C7QPilotMassActual.d S

/-- The exact generic local-field input: mK(q) = ||q||^d. -/
def MissingHaarNormIdentificationTarget : Prop :=
  EtaHaarCharNormIdentification.HaarNormIdentificationTarget
    (K := PaperKf S) (p := pNat S)

theorem localDimension_eq_d :
    EtaQHaarScalingCalibration.localDimension
      (K := PaperKf S) (p := pNat S) = C7QPilotMassActual.d S := rfl

/-- Conditional reduction of the paper qO scaling to the generic local-field
norm identification. -/
theorem paperKfQORegionScaling_of_haarNorm
    (h : EtaHaarCharNormIdentification.HaarNormIdentificationTarget
      (K := PaperKf S) (p := pNat S)) :
    ∀ q : (PaperKf S)ˣ, PaperKfQORegionScaling S q := by
  intro q
  haveI : Measure.IsAddHaarMeasure (paperKfAddHaar S) := by
    unfold paperKfAddHaar
    infer_instance
  haveI : Measure.IsAddHaarMeasure (paperKfNormalizedHaar S) :=
    paperKfNormalizedHaar_isHaar S
  haveI : (paperKfNormalizedHaar S).Regular := by
    unfold paperKfNormalizedHaar
    exact MeasureTheory.Measure.Regular.smul (μ := paperKfAddHaar S)
      (ENNReal.inv_ne_top.mpr (by
        exact (measure_localIntegers_pos_lt_top
          (K := PaperKf S) (Measure.addHaar : Measure (PaperKf S))).1.ne'))
  rw [PaperKfQORegionScaling, paperQORegion]
  have hsm := EtaQHaarScalingCalibration.measure_units_smul
    (K := PaperKf S) (paperKfNormalizedHaar S) q
    (Integers (PaperKf S) : Set (PaperKf S))
  rw [paperKfNormalizedHaar_integers] at hsm
  rw [hsm, mul_one,
    ENNReal.toReal_ofReal (EtaQHaarScalingCalibration.mK_pos
      (K := PaperKf S) q).le]
  simpa [EtaQHaarScalingCalibration.mK, localDimension_eq_d S] using h q

end LeanFormal.IUT.N8Closure.PaperKfQOScalingGeneral

end