import tmp.sheaf.n8.closure.P6RelaxedGlobalClosed
import tmp.sheaf.n8.closure.P6ArchReadoutActual

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# Numerical global relaxed readout

Combines the corrected finite+archimedean region/Adm component
`P6RelaxedGlobalClosed.relaxedGlobalReadoutClosed` with logdescent's actual
numerical archimedean readout `P6ArchReadoutActual.archReadout` (actual
infinite-place multiplicity and actual ell_out value).  The archimedean
numerical gap is thereby replaced by actual data; no arbitrary weight is used.
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
open LeanFormal.IUT.N8Closure.P6FinitePlaceReadoutActual
open LeanFormal.IUT.N8Closure.P6RelaxedReadoutActual
open LeanFormal.IUT.N8Closure.P6RelaxedGlobalReadout
open LeanFormal.IUT.N8Closure.P6RelaxedGlobalClosed
open LeanFormal.IUT.N8Closure.P6ArchReadoutActual

namespace LeanFormal.IUT.N8Closure.P6RelaxedGlobalNumerical

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
  [∀ v : NativePlaces X.S, ProperSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, Measure.IsOpenPosMeasure (mu v)]
  [∀ v : NativePlaces X.S, IsFiniteMeasureOnCompacts (mu v)]

/-- Numerical global relaxed readout: actual finite readout + actual
archimedean readout with actual numeric value. -/
structure NumericalGlobalReadout where
  finite : RelaxedFiniteReadout (X := X) (mu := mu)
  arch : ArchReadout (X := X) (mu := mu)
  value : ℝ
  value_eq : value = finite.value + arch.value

/-- Actual numerical global relaxed readout.  The archimedean component is
logdescent's actual `archReadout`; no arbitrary archimedean weight/value. -/
noncomputable def numericalGlobalReadout
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproperFinite : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v))
    (hproperArch : ∀ v : ArchimedeanPlaces (X := X),
      ProperSpace (localFieldAt X v.1)) :
    NumericalGlobalReadout (X := X) (mu := mu) := by
  let G := relaxedGlobalReadoutClosed (X := X) (mu := mu)
    hultra hproperFinite
  let A := archReadout (X := X) (mu := mu) hproperArch
  exact ⟨G.finite, A, G.finite.value + A.value, rfl⟩

theorem numericalGlobalReadout_value_eq
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproperFinite : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v))
    (hproperArch : ∀ v : ArchimedeanPlaces (X := X),
      ProperSpace (localFieldAt X v.1)) :
    (numericalGlobalReadout (X := X) (mu := mu)
      hultra hproperFinite hproperArch).value =
      (relaxedGlobalReadoutClosed (X := X) (mu := mu)
        hultra hproperFinite).finite.value +
      (archReadout (X := X) (mu := mu) hproperArch).value := rfl

theorem numericalGlobalReadout_nonempty
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproperFinite : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v))
    (hproperArch : ∀ v : ArchimedeanPlaces (X := X),
      ProperSpace (localFieldAt X v.1)) :
    Nonempty (NumericalGlobalReadout (X := X) (mu := mu)) :=
  ⟨numericalGlobalReadout (X := X) (mu := mu)
    hultra hproperFinite hproperArch⟩

end LeanFormal.IUT.N8Closure.P6RelaxedGlobalNumerical

end
