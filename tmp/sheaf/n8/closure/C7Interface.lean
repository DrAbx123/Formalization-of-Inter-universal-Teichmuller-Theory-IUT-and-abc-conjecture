import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import Mathlib

/-!
# C7 interface: C5 permitted families and C6 product/volume input

Interface module extracted from SourceHolomorphicHull to break the import cycle
with C6ProductBridge.  It contains only the C5/C6 handoff data consumed by C7.
-/

noncomputable section

namespace ABCBridge.N8.C7Actual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open MeasureTheory

universe uv ui uL uY uK

variable {l : PrimeGeFive} {V : Type uv} {Label : Type uL} [Group Label]

/-- C5 handoff: the actual permitted label family and its pilot label. -/
structure C5PermittedFamilyData where
  permitted : Set (SignedLabel l.value)
  permitted_nonempty : permitted.Nonempty
  pilotLabel : SignedLabel l.value
  pilotLabel_mem : pilotLabel ∈ permitted

/-- C6 handoff: the actual finite product of proper normed local fields, the
normalized Haar measure, and the source carrier equivalence. -/
structure C6ProductVolumeData (Y : Type uY) where
  ι : Type ui
  [finiteIndex : Finite ι]
  K : ι → Type uK
  [normedField : ∀ i, NormedField (K i)]
  [properSpace : ∀ i, ProperSpace (K i)]
  [measurableSpace : MeasurableSpace ((i : ι) → K i)]
  carrierEquiv : Y ≃ ((i : ι) → K i)
  μ : Measure ((i : ι) → K i)
  [finiteMeasureOnCompacts : IsFiniteMeasureOnCompacts μ]
  [openPosMeasure : Measure.IsOpenPosMeasure μ]

attribute [instance] C6ProductVolumeData.finiteIndex
attribute [instance] C6ProductVolumeData.normedField
attribute [instance] C6ProductVolumeData.properSpace
attribute [instance] C6ProductVolumeData.measurableSpace
attribute [instance] C6ProductVolumeData.finiteMeasureOnCompacts
attribute [instance] C6ProductVolumeData.openPosMeasure

end ABCBridge.N8.C7Actual
end
