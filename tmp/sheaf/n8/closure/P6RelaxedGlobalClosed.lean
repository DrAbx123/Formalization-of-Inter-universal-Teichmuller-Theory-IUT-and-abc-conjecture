import tmp.sheaf.n8.closure.P6RelaxedGlobalReadout

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# Corrected global relaxed readout: actual archimedean unit ball

Uses the same actual archimedean unit-ball region as logdescent's
`P6ArchimedeanRelaxedAdm` and constructs its relaxed Adm directly from
`Metric.measure_ball_pos` and `measure_ball_lt_top`.  No arbitrary archimedean
region is chosen.

The corrected global readout keeps the actual finite relaxed readout and the
actual archimedean unit-ball Adm.  Archimedean numerical weights/readout are
not asserted; that is a downstream logdescent gap.
-/

noncomputable section

open MeasureTheory BigOperators Set Metric
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

namespace LeanFormal.IUT.N8Closure.P6RelaxedGlobalClosed

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

/-- Actual archimedean unit-ball region (same region as logdescent's
`P6ArchimedeanRelaxedAdm.unitBall`). -/
def archUnitBall (v : ArchimedeanPlaces (X := X)) :
    Set (localFieldAt X v.1) :=
  Metric.ball (0 : localFieldAt X v.1) (1 : ℝ)

theorem archUnitBall_measurable (v : ArchimedeanPlaces (X := X)) :
    MeasurableSet (archUnitBall (X := X) v) :=
  measurableSet_ball

theorem archUnitBall_mass_pos_lt_top (v : ArchimedeanPlaces (X := X)) :
    0 < mu v.1 (archUnitBall (X := X) v) ∧
      mu v.1 (archUnitBall (X := X) v) < ⊤ := by
  refine ⟨?_, ?_⟩
  · exact Metric.measure_ball_pos (mu v.1) (0 : localFieldAt X v.1) zero_lt_one
  · exact measure_ball_lt_top

/-- Actual relaxed Adm for the archimedean unit ball. -/
theorem archAdm_unitBall :
    ArchAdm (X := X) (mu := mu)
      (fun v => archUnitBall (X := X) v)
      (fun v => archUnitBall (X := X) v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v; exact archUnitBall_measurable (X := X) v
  · intro v; exact (archUnitBall_mass_pos_lt_top (X := X) (mu := mu) v).1
  · intro v; exact (archUnitBall_mass_pos_lt_top (X := X) (mu := mu) v).2
  · intro v; exact archUnitBall_measurable (X := X) v
  · intro v; exact (archUnitBall_mass_pos_lt_top (X := X) (mu := mu) v).1
  · intro v; exact (archUnitBall_mass_pos_lt_top (X := X) (mu := mu) v).2

/-- Corrected archimedean component: actual region and actual relaxed Adm. -/
structure ArchReadoutClosed where
  reference : (v : ArchimedeanPlaces (X := X)) → Set (localFieldAt X v.1)
  region : (v : ArchimedeanPlaces (X := X)) → Set (localFieldAt X v.1)
  adm : ArchAdm (X := X) (mu := mu) reference region

noncomputable def archReadoutClosed :
    ArchReadoutClosed (X := X) (mu := mu) where
  reference := fun v => archUnitBall (X := X) v
  region := fun v => archUnitBall (X := X) v
  adm := archAdm_unitBall (X := X) (mu := mu)

/-- Corrected global relaxed readout: actual finite part + actual arch Adm. -/
structure RelaxedGlobalReadoutClosed where
  finite : RelaxedFiniteReadout (X := X) (mu := mu)
  arch : ArchReadoutClosed (X := X) (mu := mu)

noncomputable def relaxedGlobalReadoutClosed
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproperFinite : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v)) :
    RelaxedGlobalReadoutClosed (X := X) (mu := mu) where
  finite := relaxedFiniteReadout (X := X) (mu := mu) hultra hproperFinite
  arch := archReadoutClosed (X := X) (mu := mu)

theorem archReadoutClosed_nonempty :
    Nonempty (ArchReadoutClosed (X := X) (mu := mu)) :=
  ⟨archReadoutClosed (X := X) (mu := mu)⟩

end LeanFormal.IUT.N8Closure.P6RelaxedGlobalClosed

end
