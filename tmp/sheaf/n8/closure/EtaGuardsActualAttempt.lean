import tmp.sheaf.n8.closure.P6RelaxedNondegenerateReadout
import tmp.sheaf.n8.closure.EtaRssLogShellLine
import tmp.sheaf.n8.closure.EtaValueGroupLineActual
import tmp.sheaf.n8.closure.P6L

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaGuardsActualAttempt

universe u

open MeasureTheory BigOperators Set
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6NonarchAdmActual
open LeanFormal.IUT.N8Closure.P6FiniteSupportSourceAttempt
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6FinitePlaceReadoutActual
open LeanFormal.IUT.N8Closure.P6RelaxedReadoutActual
open LeanFormal.IUT.N8Closure.P6RelaxedNondegenerateReadout
open LeanFormal.IUT.N8Closure.EtaValueGroupLineActual
open LeanFormal.IUT.N8Closure.EtaRssLogShellLine

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-! ## Actual F-place readout guards -/

/-- Actual Theta candidate from the nondegenerate finite F-place readout. -/
noncomputable def etaThetaActual
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproper : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v)) : ℝ :=
  (nondegenerateFiniteReadout (X := X) (mu := mu) hultra hproper).value

theorem etaThetaActual_ne_zero
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproper : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v)) :
    etaThetaActual (X := X) (mu := mu) hultra hproper ≠ 0 :=
  nondegenerateFiniteReadout_value_ne_zero (X := X) (mu := mu) hultra hproper

/-- Actual Values candidate: the singleton of the actual finite readout value. -/
noncomputable def etaValuesActual
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproper : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v)) : Set ℝ :=
  {etaThetaActual (X := X) (mu := mu) hultra hproper}

theorem etaValuesActual_ne_singleton
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproper : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v)) :
    etaValuesActual (X := X) (mu := mu) hultra hproper ≠ ({0} : Set ℝ) := by
  intro h
  have hmem : etaThetaActual (X := X) (mu := mu) hultra hproper ∈
      ({0} : Set ℝ) := by
    rw [← h]
    exact mem_singleton _
  have hzero : etaThetaActual (X := X) (mu := mu) hultra hproper = 0 :=
    mem_singleton_iff.mp hmem
  exact etaThetaActual_ne_zero (X := X) (mu := mu) hultra hproper hzero

/-- Actual reference family: closed unit balls at finite places. -/
def etaReferenceActual : (v : FinitePlaces (X := X)) → Set (localFieldAt X v.1) :=
  fun v => Metric.closedBall (0 : localFieldAt X v.1) 1

/-- Actual region family: open unit balls at finite places. -/
def etaRegionActual : (v : FinitePlaces (X := X)) → Set (localFieldAt X v.1) :=
  fun v => Metric.ball (0 : localFieldAt X v.1) 1

theorem etaReferenceActual_ne_region :
    etaReferenceActual (X := X) ≠ etaRegionActual (X := X) := by
  intro h
  let v : FinitePlaces (X := X) := badFinitePlace (X := X)
  have hv := congrFun h v
  have hmem : (1 : localFieldAt X v.1) ∈ etaReferenceActual (X := X) v := by
    simp [etaReferenceActual, Metric.mem_closedBall, norm_one]
  have hnot : (1 : localFieldAt X v.1) ∉ etaRegionActual (X := X) v := by
    simp [etaRegionActual, Metric.mem_ball, norm_one]
  exact hnot (hv ▸ hmem)

/-! ## Actual guard bundle -/

structure EtaActualFPlaceGuards (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)] where
  theta : ℝ
  theta_ne_zero : theta ≠ 0
  values : Set ℝ
  values_ne_singleton : values ≠ ({0} : Set ℝ)
  reference : (v : FinitePlaces (X := X)) → Set (localFieldAt X v.1)
  region : (v : FinitePlaces (X := X)) → Set (localFieldAt X v.1)
  reference_ne_region : reference ≠ region

noncomputable def etaActualFPlaceGuards
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproper : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v)) :
    EtaActualFPlaceGuards (X := X) (mu := mu) where
  theta := etaThetaActual (X := X) (mu := mu) hultra hproper
  theta_ne_zero := etaThetaActual_ne_zero (X := X) (mu := mu) hultra hproper
  values := etaValuesActual (X := X) (mu := mu) hultra hproper
  values_ne_singleton := etaValuesActual_ne_singleton (X := X) (mu := mu) hultra hproper
  reference := etaReferenceActual (X := X)
  region := etaRegionActual (X := X)
  reference_ne_region := etaReferenceActual_ne_region (X := X)

theorem etaActualFPlaceGuards_nonempty
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproper : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v)) :
    Nonempty (EtaActualFPlaceGuards (X := X) (mu := mu)) :=
  ⟨etaActualFPlaceGuards (X := X) (mu := mu) hultra hproper⟩

/-! ## Comparison nonconstancy: exact gap -/

/-- Exact requirement for the remaining comparison guard: an actual
nonconstant map from Rval to the log-shell Rss line.  No such production
map is constructed. -/
structure EtaComparisonNonconstantRequirement (X : N8NativeInput l) where
  comparison : Rval → EtaRssLogShellLineData X
  nonconstant : ¬ ∃ c : EtaRssLogShellLineData X,
    ∀ x : Rval, comparison x = c

end LeanFormal.IUT.N8Closure.EtaGuardsActualAttempt
