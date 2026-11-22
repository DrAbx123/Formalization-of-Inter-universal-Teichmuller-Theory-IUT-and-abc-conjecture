import tmp.sheaf.n8.closure.P6L
import Mathlib

/-!
# Archimedean relaxed Adm: actual unit ball

Constructs the actual unit ball `Metric.ball 0 1` in the archimedean local
field, proves it is measurable with positive finite additive Haar mass, and
packages it as a relaxed Adm region that does not require the local log to
vanish.  The region is fixed (unit ball), not arbitrary.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L

namespace LeanFormal.IUT.N8Closure.P6ArchimedeanRelaxedAdm

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- The actual unit-ball region at a native place. -/
def unitBall (v : NativePlaces X.S) : Set (localFieldAt X v) :=
  Metric.ball (0 : localFieldAt X v) (1 : ℝ)

/-- The global unit-ball region family. -/
def unitBallGlobal : GlobalRegion X :=
  fun v => unitBall X v

/-- Relaxed Adm at one place: measurable, positive mass, finite mass.  No
local-log condition. -/
def RelaxedAdmAt (v : NativePlaces X.S) (R : Set (localFieldAt X v)) : Prop :=
  MeasurableSet R ∧ 0 < mu v R ∧ mu v R < ⊤

/-- Relaxed global Adm: only measurability, positive mass and finite mass for
the reference and region; no a.e. local-log condition. -/
def RelaxedAdm (reference region : GlobalRegion X) : Prop :=
  (∀ v, MeasurableSet (reference v)) ∧
  (∀ v, 0 < mu v (reference v)) ∧
  (∀ v, mu v (reference v) < ⊤) ∧
  (∀ v, MeasurableSet (region v)) ∧
  (∀ v, 0 < mu v (region v)) ∧
  (∀ v, mu v (region v) < ⊤)

/-- The unit ball is measurable. -/
theorem unitBall_measurable (v : NativePlaces X.S) :
    MeasurableSet (unitBall X v) :=
  measurableSet_ball

/-- The unit ball has positive finite Haar mass at a proper local field. -/
theorem unitBall_mass_pos_lt_top
    (v : NativePlaces X.S)
    [ProperSpace (localFieldAt X v)]
    [Measure.IsOpenPosMeasure (mu v)]
    [IsFiniteMeasureOnCompacts (mu v)] :
    0 < mu v (unitBall X v) ∧ mu v (unitBall X v) < ⊤ := by
  refine ⟨?_, ?_⟩
  · exact Metric.measure_ball_pos (mu v) 0 zero_lt_one
  · exact measure_ball_lt_top

/-- The unit ball is an actual relaxed-Adm region. -/
theorem unitBall_relaxedAdmAt
    (v : NativePlaces X.S)
    [ProperSpace (localFieldAt X v)]
    [Measure.IsOpenPosMeasure (mu v)]
    [IsFiniteMeasureOnCompacts (mu v)] :
    RelaxedAdmAt (X := X) (mu := mu) v (unitBall X v) :=
  ⟨unitBall_measurable (X := X) v,
    (unitBall_mass_pos_lt_top (X := X) (mu := mu) v).1,
    (unitBall_mass_pos_lt_top (X := X) (mu := mu) v).2⟩

/-- The global unit-ball family is a relaxed global Adm pair. -/
theorem unitBallGlobal_relaxedAdm
    [∀ v : NativePlaces X.S, ProperSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, Measure.IsOpenPosMeasure (mu v)]
    [∀ v : NativePlaces X.S, IsFiniteMeasureOnCompacts (mu v)] :
    RelaxedAdm (X := X) (mu := mu) (unitBallGlobal X) (unitBallGlobal X) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v; exact unitBall_measurable (X := X) v
  · intro v; exact (unitBall_mass_pos_lt_top (X := X) (mu := mu) v).1
  · intro v; exact (unitBall_mass_pos_lt_top (X := X) (mu := mu) v).2
  · intro v; exact unitBall_measurable (X := X) v
  · intro v; exact (unitBall_mass_pos_lt_top (X := X) (mu := mu) v).1
  · intro v; exact (unitBall_mass_pos_lt_top (X := X) (mu := mu) v).2

end LeanFormal.IUT.N8Closure.P6ArchimedeanRelaxedAdm
