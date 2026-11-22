/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import tmp.sheaf.xif.paper.AbsTopIII07NormalizedLocalVolumeActual
import tmp.sheaf.xif.paper.Mzk1DetLinePrincipalGeneratorActual
import Mathlib.Tactic

/-! # CarrierEquivData: single named input for B3 carrier align + scaling -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1CarrierEquivDataActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.AbsTopIII07NormalizedLocalVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePrincipalGeneratorActual
open LeanFormal.IUT.XiFPaper.Mzk1DetLinePlaceB5Actual
variable {k : Type} [Field k] [NumberField k] {p : ℕ} [Fact p.Prime]
variable (place : FinitePlaceAtPrime k p)
local instance carrierDataMeasurable : MeasurableSpace (CommonPrimeCompletion place) := borel _
local instance completionMeasurable : MeasurableSpace (Completion place.val) := borel _
local instance carrierDataBorel : BorelSpace (CommonPrimeCompletion place) := ⟨rfl⟩

/-- Named carrier data: an explicit measurable equivalence from the B3 carrier
`CommonPrimeCompletion place` to the localized-line carrier `Completion place.val`,
together with the local Haar scaling law.  No inhabitant is asserted. -/
structure CarrierEquivData (place : FinitePlaceAtPrime k p) where
  equiv : CommonPrimeCompletion place ≃ Completion place.val
  measurable_equiv : Measurable equiv
  measurable_symm : Measurable equiv.symm
  scaling : LocalHaarScalingLaw (CommonPrimeCompletion place)

def CarrierEquivDataRequired : Prop := Nonempty (CarrierEquivData place)

/-- Rows: the three B3 gaps are now represented by one named data for carrier
align + scaling, plus the separate principal-generator bridge. -/
def carrierDataRows : List (String × String) :=
  [ ("CarrierEquivData", "named input: CommonPrimeCompletion ≃ Completion + scaling"),
    ("CarrierEquivDataRequired", "Nonempty (named input); no inhabitant"),
    ("CountLocalizationBridge", "separate GAP: localizedLine = span generator") ]
theorem carrierDataRows_length : carrierDataRows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1CarrierEquivDataActual
