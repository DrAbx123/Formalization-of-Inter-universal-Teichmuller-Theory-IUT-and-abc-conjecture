import tmp.sheaf.n8.closure.P6RelaxedReadoutActual
import tmp.sheaf.n8.closure.P6L

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

/-!
# Corrected global relaxed readout

Combines the actual finite-place relaxed readout with an archimedean branch.
The archimedean reference/region is the actual closed unit ball, not an
arbitrary region.  Its relaxed Adm (measurable + positive finite Haar mass) is
proved from properness.  The archimedean procession weights/dimensions and
readout value have no production donor, so that branch is the exact named gap.
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

namespace LeanFormal.IUT.N8Closure.P6RelaxedGlobalReadout

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Native places whose local field is archimedean. -/
abbrev ArchimedeanPlaces : Type _ :=
  {v : NativePlaces X.S // ¬ IsFiniteNativePlace X v}

/-- Actual archimedean reference/region: the closed unit ball. -/
def archClosedBall (v : ArchimedeanPlaces (X := X)) :
    Set (localFieldAt X v.1) :=
  Metric.closedBall (0 : localFieldAt X v.1) 1

/-- Relaxed archimedean Adm: measurable + positive finite Haar mass. -/
def ArchAdm
    (reference region : (v : ArchimedeanPlaces (X := X)) →
      Set (localFieldAt X v.1)) : Prop :=
  (∀ v, MeasurableSet (reference v)) ∧
  (∀ v, 0 < mu v.1 (reference v)) ∧
  (∀ v, mu v.1 (reference v) < ⊤) ∧
  (∀ v, MeasurableSet (region v)) ∧
  (∀ v, 0 < mu v.1 (region v)) ∧
  (∀ v, mu v.1 (region v) < ⊤)

/-- The actual archimedean closed unit ball has relaxed Adm under properness.
  No arbitrary archimedean region is chosen. -/
theorem archAdm_closedBall
    (hproper : ∀ v : ArchimedeanPlaces (X := X),
      ProperSpace (localFieldAt X v.1)) :
    ArchAdm (X := X) (mu := mu)
      (fun v => archClosedBall (X := X) v)
      (fun v => archClosedBall (X := X) v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v; exact Metric.isClosed_closedBall.measurableSet
  · intro v
    apply Measure.measure_pos_of_nonempty_interior
    refine ⟨(0 : localFieldAt X v.1), ?_⟩
    change (0 : localFieldAt X v.1) ∈ interior (archClosedBall (X := X) v)
    exact Metric.ball_subset_interior_closedBall (Metric.mem_ball_self zero_lt_one)
  · intro v
    letI : ProperSpace (localFieldAt X v.1) := hproper v
    exact (isCompact_closedBall (0 : localFieldAt X v.1) 1).measure_lt_top
  · intro v; exact Metric.isClosed_closedBall.measurableSet
  · intro v
    apply Measure.measure_pos_of_nonempty_interior
    refine ⟨(0 : localFieldAt X v.1), ?_⟩
    change (0 : localFieldAt X v.1) ∈ interior (archClosedBall (X := X) v)
    exact Metric.ball_subset_interior_closedBall (Metric.mem_ball_self zero_lt_one)
  · intro v
    letI : ProperSpace (localFieldAt X v.1) := hproper v
    exact (isCompact_closedBall (0 : localFieldAt X v.1) 1).measure_lt_top

/-- Archimedean readout data: actual closed-ball Adm plus procession
weights/dimensions/value.  The latter fields are the missing production
donor (no actual archimedean weights/dimensions are constructed). -/
structure ArchReadout where
  support : Finset (ArchimedeanPlaces (X := X))
  weight : ArchimedeanPlaces (X := X) → ℝ
  dimension : ArchimedeanPlaces (X := X) → ℝ
  dimension_ne_zero : ∀ v, dimension v ≠ 0
  adm : ArchAdm (X := X) (mu := mu)
    (fun v => archClosedBall (X := X) v)
    (fun v => archClosedBall (X := X) v)
  value : ℝ

/-- Corrected global relaxed readout: actual finite relaxed readout plus the
archimedean branch; frozen P6L.Adm is not used. -/
structure RelaxedGlobalReadout where
  finite : RelaxedFiniteReadout (X := X) (mu := mu)
  arch : ArchReadout (X := X) (mu := mu)

/-- Actual global reference/region/Adm for the finite and archimedean parts. -/
theorem relaxedGlobalAdm_actual
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproperFinite : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v))
    (hproperArch : ∀ v : ArchimedeanPlaces (X := X),
      ProperSpace (localFieldAt X v.1)) :
    RelaxedAdmFinite (X := X) (mu := mu)
        (fun v => unitSphereAt (X := X) v.1)
        (fun v => unitSphereAt (X := X) v.1) ∧
      ArchAdm (X := X) (mu := mu)
        (fun v => archClosedBall (X := X) v)
        (fun v => archClosedBall (X := X) v) :=
  ⟨relaxedAdmFinite_sphere (X := X) (mu := mu) hultra hproperFinite,
   archAdm_closedBall (X := X) (mu := mu) hproperArch⟩

/-- Exact missing archimedean weights/dimensions/readout value. -/
theorem missing_archReadout
    (hproperArch : ∀ v : ArchimedeanPlaces (X := X),
      ProperSpace (localFieldAt X v.1)) :
    Nonempty (ArchReadout (X := X) (mu := mu)) :=
  -- The admissible archimedean reference/region is the actual closed unit ball
  -- (archAdm_closedBall from properness); the procession weight/dimension/value
  -- are free fields of the structure, so existence follows structurally.
  ⟨{ support := ∅
     weight := fun _ => 0
     dimension := fun _ => 1
     dimension_ne_zero := fun _ => one_ne_zero
     adm := archAdm_closedBall (X := X) (mu := mu) hproperArch
     value := 0 }⟩

end LeanFormal.IUT.N8Closure.P6RelaxedGlobalReadout

end
