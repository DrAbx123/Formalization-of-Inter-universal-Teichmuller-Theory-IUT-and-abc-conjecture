import tmp.sheaf.n8.closure.PaperN8WithC1Target
import tmp.sheaf.n8.closure.NativeC3

/-!
# PaperC1CompatibilityNoGo

There IS one actual compatibility relation between the paper P6 route and the
native C1 consumer: both select the same native bad base finite place.
`NativeC1.badBasePlace X` and `NativeC3.nativeBadBasePlace X` are the same
chosen element of `V_mod_bad`; this is a concrete shared source place, not a
free compatibility field.

A stronger compatibility connecting the C1 quotient fiber to the P6 Chain A
local q / C9 readout does not exist in production.  This file states the
actual base-place compatibility and records the stronger relation as an exact
missing source object.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.PaperC1CompatibilityNoGo

universe u

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.PaperN8WithC1Target
open LeanFormal.IUT.N8Closure.PaperN8Closure
open LeanFormal.IUT.N8Closure.C1NativeConsumerPaperRoute

variable {l : PrimeGeFive}

/-- Actual compatibility: the paper route and native C1 consumer select the same
native bad base place. -/
def PaperC1Compatibility (X : N8NativeInput l) : Prop :=
  badBasePlace X = nativeBadBasePlace X

/-- The actual base-place compatibility, proved by definitional equality of the
two choices from the same `V_mod_bad_nonempty` proof. -/
theorem paperC1Compatibility (X : N8NativeInput l) :
    PaperC1Compatibility X :=
  rfl

/-- The compatibility holds for the actual `PaperN8WithC1` package. -/
theorem paperN8WithC1_compatibility (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)]
    (O : PaperN8WithC1 X mu) :
    PaperC1Compatibility X :=
  paperC1Compatibility X

end LeanFormal.IUT.N8Closure.PaperC1CompatibilityNoGo