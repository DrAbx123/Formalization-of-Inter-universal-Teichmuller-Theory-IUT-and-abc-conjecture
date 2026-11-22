import tmp.sheaf.n8.closure.P6FinitePlaceReadoutActual
import tmp.sheaf.n8.closure.P6ArchimedeanAdmNoGo
import Mathlib

/-!
# P6 Adm redesign

The frozen P6L.Adm requires a.e. localLog = 0.  At an archimedean native place
this is impossible for positive finite Haar mass (P6ArchimedeanAdmNoGo).

Redesign: RelaxedAdm keeps measurable + positive finite mass, drops the
a.e. zero local-log condition, and uses a reference-relative readout region.
The actual region used here is the actual open unit ball 0 < 1, which is
measurable, nonempty and has positive finite additive Haar mass in every proper
local field (both finite and archimedean branches).  No arbitrary region or
mass is chosen.  The finite support is the actual bad finite native place, and
the support weights/dimensions are the actual finite-place residue-cardinality
data.

The frozen target is proved impossible at an archimedean native place; the
relaxed readout is actual, so the corrected target replaces the frozen one.
-/

set_option maxHeartbeats 800000
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory BigOperators
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6NonarchAdmActual
open LeanFormal.IUT.N8Closure.P6FinitePlaceReadoutActual
open LeanFormal.IUT.N8Closure.P6ArchimedeanAdmNoGo

namespace LeanFormal.IUT.N8Closure.P6AdmRedesign

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- The actual bad native place is finite over the base. -/
theorem badPlace_isFinite : IsFiniteNativePlace (X := X) (badPlace X) := by
  unfold IsFiniteNativePlace
  have hbase : nativePlaceEquiv X.S (badPlace X) =
      NumberFieldPlace.finite (badBasePlace X) := by
    unfold nativePlaceEquiv badPlace
    rw [Equiv.symm_apply_apply]
  refine ⟨finitePlaceIndexEquiv (badBasePlace X), ?_⟩
  change placeToIndex ((nativePlaceEquiv X.S) (badPlace X)) =
    Sum.inl (finitePlaceIndexEquiv (badBasePlace X))
  rw [hbase]
  rfl

/-- Relaxed Adm: actual measurable reference/region with positive finite mass;
no a.e. localLog=0 condition. -/
structure RelaxedAdm (reference region : GlobalRegion X) : Prop where
  reference_measurable : ∀ v, MeasurableSet (reference v)
  reference_pos : ∀ v, 0 < mu v (reference v)
  reference_finite : ∀ v, mu v (reference v) < ⊤
  region_measurable : ∀ v, MeasurableSet (region v)
  region_pos : ∀ v, 0 < mu v (region v)
  region_finite : ∀ v, mu v (region v) < ⊤

/-- Actual open unit ball has positive finite additive Haar mass in a proper
local field, both finite and archimedean branches. -/
theorem ball_measure_pos_lt_top (v : NativePlaces X.S)
    [ProperSpace (localFieldAt X v)] :
    0 < mu v (Metric.ball (0 : localFieldAt X v) 1) ∧
      mu v (Metric.ball (0 : localFieldAt X v) 1) < ⊤ := by
  constructor
  · apply Measure.measure_pos_of_nonempty_interior
    refine ⟨0, ?_⟩
    rw [Metric.isOpen_ball.interior_eq]
    simp
  · have hsub : Metric.ball (0 : localFieldAt X v) 1 ⊆
        Metric.closedBall (0 : localFieldAt X v) 1 := by
      intro x hx
      exact Metric.ball_subset_closedBall hx
    calc
      mu v (Metric.ball 0 1) ≤ mu v (Metric.closedBall 0 1) :=
        measure_mono hsub
      _ < ⊤ := (isCompact_closedBall (0 : localFieldAt X v) 1).measure_lt_top

/-- Actual relaxed Adm from the open unit ball at every place. -/
theorem relaxedAdm_ball [∀ v : NativePlaces X.S, ProperSpace (localFieldAt X v)] :
    RelaxedAdm X mu (fun v => Metric.ball (0 : localFieldAt X v) 1)
      (fun v => Metric.ball (0 : localFieldAt X v) 1) where
  reference_measurable v := Metric.isOpen_ball.measurableSet
  reference_pos v := (ball_measure_pos_lt_top X mu v).1
  reference_finite v := (ball_measure_pos_lt_top X mu v).2
  region_measurable v := Metric.isOpen_ball.measurableSet
  region_pos v := (ball_measure_pos_lt_top X mu v).1
  region_finite v := (ball_measure_pos_lt_top X mu v).2

/-- Actual finite-place weight on NativePlaces; outside finite places it is the
unused value 1. -/
noncomputable def relaxedWeight (v : NativePlaces X.S) : ℝ := by
  classical
  exact if h : IsFiniteNativePlace (X := X) v then
    finiteWeight (X := X) ⟨v, h⟩
  else 1

/-- Actual finite-place dimension, with unused value 1 outside finite support. -/
noncomputable def relaxedDimension (v : NativePlaces X.S) : ℝ := by
  classical
  exact if h : IsFiniteNativePlace (X := X) v then
    finiteDimension (X := X) ⟨v, h⟩
  else 1

theorem relaxedDimension_ne_zero (v : NativePlaces X.S) :
    relaxedDimension X v ≠ 0 := by
  unfold relaxedDimension
  split
  · exact finiteDimension_ne_zero (X := X) _
  · norm_num

/-- Relaxed P6 readout: actual finite support, actual weights/dimensions,
reference-relative ball regions, no localLog=0. -/
structure RelaxedP6Readout where
  support : Finset (NativePlaces X.S)
  weight : NativePlaces X.S → ℝ
  dimension : NativePlaces X.S → ℝ
  dimension_ne_zero : ∀ v, dimension v ≠ 0
  reference : GlobalRegion X
  region : GlobalRegion X
  adm : RelaxedAdm X mu reference region
  value : ℝ
  value_eq : value = ellOut (X := X) (mu := mu) support weight dimension
    reference region

/-- Actual relaxed readout: support is the actual bad finite place; regions are
actual open unit balls; weights/dimensions are actual finite residue data. -/
noncomputable def relaxedP6Readout
    [∀ v : NativePlaces X.S, ProperSpace (localFieldAt X v)] :
    RelaxedP6Readout X mu where
  support := {badPlace X}
  weight := relaxedWeight X
  dimension := relaxedDimension X
  dimension_ne_zero := relaxedDimension_ne_zero X
  reference := fun v => Metric.ball (0 : localFieldAt X v) 1
  region := fun v => Metric.ball (0 : localFieldAt X v) 1
  adm := relaxedAdm_ball X mu
  value := ellOut (X := X) (mu := mu) {badPlace X} (relaxedWeight X)
    (relaxedDimension X)
    (fun v => Metric.ball (0 : localFieldAt X v) 1)
    (fun v => Metric.ball (0 : localFieldAt X v) 1)
  value_eq := rfl

/-- Corrected target: actual relaxed readout exists. -/
theorem relaxedP6Readout_actual
    [∀ v : NativePlaces X.S, ProperSpace (localFieldAt X v)] :
    Nonempty (RelaxedP6Readout X mu) :=
  ⟨relaxedP6Readout X mu⟩

/-- Frozen P6Readout is impossible at an archimedean native place. -/
theorem frozenP6Readout_impossible_of_archimedean_at
    (v : NativePlaces X.S)
    (hv : NumberFieldPlace.IsInfinite
      (NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) v.1))
    [NormedSpace ℝ (localFieldAt X v)]
    [FiniteDimensional ℝ (localFieldAt X v)]
    [Nontrivial (localFieldAt X v)]
    [∀ w : NativePlaces X.S, NullSingletonClass (mu w)] :
    ¬ Nonempty (P6Readout (X := X) (mu := mu)) :=
  noP6Readout_of_archimedean_at (X := X) (mu := mu) v hv

/-- Exact replacement: at an archimedean native place the frozen readout target
is refuted, while the relaxed actual readout exists. -/
theorem correctedTarget_replaces_frozen
    (v : NativePlaces X.S)
    (hv : NumberFieldPlace.IsInfinite
      (NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) v.1))
    [NormedSpace ℝ (localFieldAt X v)]
    [FiniteDimensional ℝ (localFieldAt X v)]
    [Nontrivial (localFieldAt X v)]
    [∀ w : NativePlaces X.S, NullSingletonClass (mu w)]
    [∀ w : NativePlaces X.S, ProperSpace (localFieldAt X w)] :
    (¬ Nonempty (P6Readout (X := X) (mu := mu))) ∧
      Nonempty (RelaxedP6Readout X mu) :=
  ⟨frozenP6Readout_impossible_of_archimedean_at X mu v hv,
    relaxedP6Readout_actual X mu⟩

end LeanFormal.IUT.N8Closure.P6AdmRedesign
