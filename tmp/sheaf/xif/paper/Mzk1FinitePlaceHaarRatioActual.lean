/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.AbsTopIII07NormalizedLocalVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePlaceB5Actual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import Mathlib.Tactic

/-! # B3 finite-place Haar ratio on CommonPrimeCompletion (conditional) -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Metric
namespace LeanFormal.IUT.XiFPaper.Mzk1FinitePlaceHaarRatioActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.AbsTopIII07NormalizedLocalVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)
abbrev carrier := CommonPrimeCompletion place
local instance carrierMeasurable : MeasurableSpace (carrier place) := borel _
local instance carrierBorel : BorelSpace (carrier place) := ⟨rfl⟩

theorem normalizedHaar_scaled_unitBall
    (h : LocalHaarScalingLaw (carrier place)) (a : carrier place) :
    normalizedHaar (K := carrier place) ((fun x : carrier place => a * x) '' unitBall (K := carrier place)) =
      (‖a‖₊ : ENNReal) := by
  rw [h a (unitBall (K := carrier place)) (unitBall_isOpen (K := carrier place)).measurableSet,
    normalizedHaar_unitBall]
  exact mul_one (‖a‖₊ : ENNReal)

theorem b3_ratio_scaled_unitBall
    (h : LocalHaarScalingLaw (carrier place)) (a : carrier place) :
    normalizedHaar (K := carrier place) ((fun x : carrier place => a * x) '' unitBall (K := carrier place)) /
        normalizedHaar (K := carrier place) (unitBall (K := carrier place)) = (‖a‖₊ : ENNReal) := by
  rw [normalizedHaar_scaled_unitBall (place := place) h a, normalizedHaar_unitBall]
  exact div_one (‖a‖₊ : ENNReal)

def b3Rows : List (String × String) :=
  [ ("normalizedHaar_scaled_unitBall", "carrier=CommonPrimeCompletion; conditional scaling law"),
    ("b3_ratio_scaled_unitBall", "reference-lattice ratio = ||a||"),
    ("localizedLine generator link", "GAP: CountLocalizationBridge"),
    ("LocalHaarScalingLaw", "GAP: AbsTopIII Prop5.7") ]
theorem b3Rows_length : b3Rows.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1FinitePlaceHaarRatioActual
