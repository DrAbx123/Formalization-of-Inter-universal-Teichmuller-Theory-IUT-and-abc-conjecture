import tmp.sheaf.n8.closure.P6AdmRedesign
import tmp.sheaf.n8.closure.P6NonarchAdmActual
import tmp.sheaf.n8.closure.NativeC1

/-!
# Eta region-type Adm correction

Replaces the frozen pointwise a.e. localLog=0 condition by a finite-support
region condition:

  exists finite T, forall v notin T, region v = reference v

so the local readout vanishes outside a finite support.  The reference is the
actual integral structure: the nonarchimedean unit sphere at finite native
places and the actual open unit ball at archimedean native places.  The region
is the actual unit ball at the bad finite place and equals the reference
elsewhere.

No unsourced point log condition is introduced.  The construction is actual;
no named gap is needed.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaRegionAdmCorrect

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6NonarchAdmActual
open LeanFormal.IUT.N8Closure.P6AdmRedesign

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
variable [∀ v : NativePlaces X.S, ProperSpace (localFieldAt X v)]
variable (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace (X := X) v →
  IsUltrametricDist (localFieldAt X v))

include hultra

/-- Actual source reference from the integral structure: nonarch unit sphere at
finite native places, open unit ball at archimedean places. -/
noncomputable def integralReference : GlobalRegion X := by
  classical
  exact fun v =>
    if IsFiniteNativePlace (X := X) v then
      unitSphereAt (X := X) v
    else
      Metric.ball (0 : localFieldAt X v) (1 : ℝ)

/-- Actual region: open unit ball at the bad finite place; reference elsewhere. -/
noncomputable def correctedRegion : GlobalRegion X := by
  classical
  exact fun v =>
    if v = badPlace X then
      Metric.ball (0 : localFieldAt X v) (1 : ℝ)
    else
      integralReference X v

/-- Region-type corrected Adm: measurable positive finite reference/region and
finite-support agreement, no pointwise localLog condition. -/
structure RegionAdmCorrect (reference region : GlobalRegion X) : Prop where
  finiteSupport : ∃ T : Finset (NativePlaces X.S),
    ∀ v : NativePlaces X.S, v ∉ T → region v = reference v
  reference_measurable : ∀ v, MeasurableSet (reference v)
  reference_pos : ∀ v, 0 < mu v (reference v)
  reference_finite : ∀ v, mu v (reference v) < ⊤
  region_measurable : ∀ v, MeasurableSet (region v)
  region_pos : ∀ v, 0 < mu v (region v)
  region_finite : ∀ v, mu v (region v) < ⊤

theorem integralReference_measurable (v : NativePlaces X.S) :
    MeasurableSet (integralReference X v) := by
  unfold integralReference
  split
  · exact unitSphereAt_measurable (X := X) v
  · exact Metric.isOpen_ball.measurableSet

theorem integralReference_pos (v : NativePlaces X.S) :
    0 < mu v (integralReference X v) := by
  unfold integralReference
  by_cases h : IsFiniteNativePlace (X := X) v
  · rw [if_pos h]
    letI : IsUltrametricDist (localFieldAt X v) := hultra v h
    exact (P6NonarchSphereMassActual.unitSphere_measure_pos_lt_top
      (K := localFieldAt X v) (mu v)).1
  · rw [if_neg h]
    exact (P6AdmRedesign.ball_measure_pos_lt_top X mu v).1

theorem integralReference_finite (v : NativePlaces X.S) :
    mu v (integralReference X v) < ⊤ := by
  unfold integralReference
  by_cases h : IsFiniteNativePlace (X := X) v
  · rw [if_pos h]
    letI : IsUltrametricDist (localFieldAt X v) := hultra v h
    exact (P6NonarchSphereMassActual.unitSphere_measure_pos_lt_top
      (K := localFieldAt X v) (mu v)).2
  · rw [if_neg h]
    exact (P6AdmRedesign.ball_measure_pos_lt_top X mu v).2

theorem correctedRegion_measurable (v : NativePlaces X.S) :
    MeasurableSet (correctedRegion X v) := by
  unfold correctedRegion
  split
  · exact Metric.isOpen_ball.measurableSet
  · exact integralReference_measurable X hultra v

theorem correctedRegion_pos (v : NativePlaces X.S) :
    0 < mu v (correctedRegion X v) := by
  unfold correctedRegion
  split
  · exact (P6AdmRedesign.ball_measure_pos_lt_top X mu v).1
  · exact integralReference_pos X mu hultra v

theorem correctedRegion_finite (v : NativePlaces X.S) :
    mu v (correctedRegion X v) < ⊤ := by
  unfold correctedRegion
  split
  · exact (P6AdmRedesign.ball_measure_pos_lt_top X mu v).2
  · exact integralReference_finite X mu hultra v

/-- Actual corrected region Adm. -/
noncomputable def etaRegionAdmCorrect :
    RegionAdmCorrect X mu (integralReference X) (correctedRegion X) where
  finiteSupport := by
    refine ⟨{badPlace X}, ?_⟩
    intro v hv
    unfold correctedRegion
    rw [if_neg]
    exact fun h => hv (by simpa [h])
  reference_measurable := integralReference_measurable X hultra
  reference_pos := integralReference_pos X mu hultra
  reference_finite := integralReference_finite X mu hultra
  region_measurable := correctedRegion_measurable X hultra
  region_pos := correctedRegion_pos X mu hultra
  region_finite := correctedRegion_finite X mu hultra

/-- Exact target class: corrected region Adm is actually inhabited. -/
def EtaRegionAdmCorrectTarget (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
    [∀ v : NativePlaces X.S, ProperSpace (localFieldAt X v)]
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace (X := X) v →
      IsUltrametricDist (localFieldAt X v)) : Prop :=
  ∃ (reference region : GlobalRegion X), RegionAdmCorrect X mu reference region

theorem etaRegionAdmCorrectTarget_actual
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
    [∀ v : NativePlaces X.S, ProperSpace (localFieldAt X v)]
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace (X := X) v →
      IsUltrametricDist (localFieldAt X v)) :
    EtaRegionAdmCorrectTarget X mu hultra :=
  ⟨integralReference X, correctedRegion X, etaRegionAdmCorrect X mu hultra⟩

end LeanFormal.IUT.N8Closure.EtaRegionAdmCorrect
