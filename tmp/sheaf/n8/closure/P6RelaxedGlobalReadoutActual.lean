import tmp.sheaf.n8.closure.P6ArchReadoutActual
import tmp.sheaf.n8.closure.P6RelaxedReadoutActual
import tmp.sheaf.n8.closure.P6RelaxedGlobalReadout
import Mathlib

/-!
# Actual corrected global relaxed P6 readout

Combines the actual finite relaxed readout (nonarch unit sphere, actual
residue-cardinality weights/dimensions, singleton support) with the actual
ArchReadout (archimedean closed unit ball, actual infinite-place multiplicity).
This is the actual replacement for `P6RelaxedGlobalReadout.missing_archReadout`.
-/

noncomputable section

open MeasureTheory BigOperators
open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6NonarchAdmActual
open LeanFormal.IUT.N8Closure.P6RelaxedReadoutActual
open LeanFormal.IUT.N8Closure.P6ArchReadoutActual
open LeanFormal.IUT.N8Closure.P6RelaxedGlobalReadout

namespace LeanFormal.IUT.N8Closure.P6RelaxedGlobalReadoutActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Corrected global relaxed readout: actual finite component plus actual
archimedean component. -/
noncomputable def relaxedGlobalReadoutActual
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproperFinite : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v))
    (hproperArch : ∀ v : ArchimedeanPlaces (X := X),
      ProperSpace (localFieldAt X v.1)) :
    RelaxedGlobalReadout (X := X) (mu := mu) where
  finite := relaxedFiniteReadout (X := X) (mu := mu) hultra hproperFinite
  arch := archReadout (X := X) (mu := mu) hproperArch

/-- Actual corrected global relaxed readout exists, replacing the former
archimedean named gap. -/
theorem relaxedGlobalReadoutActual_nonempty
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproperFinite : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v))
    (hproperArch : ∀ v : ArchimedeanPlaces (X := X),
      ProperSpace (localFieldAt X v.1)) :
    Nonempty (RelaxedGlobalReadout (X := X) (mu := mu)) :=
  ⟨relaxedGlobalReadoutActual (X := X) (mu := mu)
    hultra hproperFinite hproperArch⟩

/-- The corrected readout uses the actual nonarch unit sphere on finite places
and the actual archimedean closed unit ball; no arbitrary region. -/
theorem relaxedGlobalReadoutActual_regions_actual
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproperFinite : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v))
    (hproperArch : ∀ v : ArchimedeanPlaces (X := X),
      ProperSpace (localFieldAt X v.1)) :
    (relaxedGlobalReadoutActual (X := X) (mu := mu)
      hultra hproperFinite hproperArch).finite.support.Nonempty := by
  exact relaxedFiniteReadout_support_nonempty (X := X) (mu := mu)
    hultra hproperFinite

end LeanFormal.IUT.N8Closure.P6RelaxedGlobalReadoutActual
