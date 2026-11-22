import tmp.sheaf.xif.paper.RootHullMeasureActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Global qVFamily product carrier and global hull/mu_log

The per-b coefficient has its own rational prime p_b, so there is no single
ArithmeticTensorTupleBlock over all bad places.  The actual global carrier is
the product

  QVFamProductCarrier T = (b : Bad ...) -> qVFamTensorBlock T b,

with the product Haar measure Measure.pi mu and the global root hull

  globalRootHull = Set.pi univ (fun b => rootNormHull T b).

Its normalized log is the sum of the actual per-b normalized logs.  The global
q-pilot region is the product of the per-b q-pilot regions; it is contained in
the global root hull pointwise, and the global q-pilot log is <= the global
root hull log by summing the actual per-b inequalities.

No single fixed-p tensor block is claimed.  No fake equality/Haar/axiom/sorry.
-/

noncomputable section
open scoped BigOperators Pointwise ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.QVFamGlobalProductCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open MeasureTheory
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual mixed-prime global product carrier. -/
abbrev QVFamProductCarrier : Type :=
  (b : Bad (nativePlaceSelection T)) → qVFamTensorBlock T b

/-- The actual global root hull, fiberwise over bad places. -/
noncomputable def globalRootHull : Set (QVFamProductCarrier T) :=
  Set.pi Set.univ (fun b => rootNormHull (l := l) T b)

/-- The actual global q-pilot region, fiberwise. -/
noncomputable def globalQPilotRegion : Set (QVFamProductCarrier T) :=
  Set.pi Set.univ (fun b => qPilotNormRegion (l := l) T b)

/- Actual per-b measurable/Borel/Haar data. -/
variable [∀ b, MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b, BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b, Measure (qVFamTensorBlock T b))
variable [∀ b, Measure.IsAddHaarMeasure (mu b)]

/-- The actual product Haar measure on the mixed-prime carrier. -/
noncomputable def globalProductHaar
    (mu : ∀ b, Measure (qVFamTensorBlock T b)) :
    Measure (QVFamProductCarrier T) :=
  Measure.pi (fun b => mu b)

/-- The actual global root hull Haar value. -/
noncomputable def globalRootHullHaar
    (mu : ∀ b, Measure (qVFamTensorBlock T b)) : ENNReal :=
  (globalProductHaar (T := T) (mu := mu)) (globalRootHull T)

/-- The actual global q-pilot region Haar value. -/
noncomputable def globalQPilotRegionHaar
    (mu : ∀ b, Measure (qVFamTensorBlock T b)) : ENNReal :=
  (globalProductHaar (T := T) (mu := mu)) (globalQPilotRegion T)

/-- The actual global q-pilot normalized log: sum over b of the per-b q-pilot
normalized logs. -/
noncomputable def globalQPilotLog
    (mu : ∀ b, Measure (qVFamTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (mu b)] : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual.qPilotClassicalLog
      (places := qVFamTensorPlaces T b)
      (tuple := qVFamTensorTuple)
      (μ := mu b)
      (cNorm := rootNormCoefficient (l := l) T b)
      (rootNormScalingData (l := l) T b)

/-- The actual global root hull normalized log: sum over b of the per-b root
hull normalized logs. -/
noncomputable def globalRootHullLog
    (mu : ∀ b, Measure (qVFamTensorBlock T b)) : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual.rootThetaHullLog (l := l)
      (places := qVFamTensorPlaces T b)
      (tuple := qVFamTensorTuple)
      (μ := mu b)
      (cRoot := rootHalfCoefficient (l := l) T b)

/-- Pointwise global hull membership is exactly fiberwise hull membership. -/
theorem mem_globalRootHull_iff (x : QVFamProductCarrier T) :
    x ∈ globalRootHull T ↔
      ∀ b, x b ∈ rootNormHull (l := l) T b := by
  simp [globalRootHull]

/-- Pointwise global q-pilot membership is exactly fiberwise q-pilot membership. -/
theorem mem_globalQPilotRegion_iff (x : QVFamProductCarrier T) :
    x ∈ globalQPilotRegion T ↔
      ∀ b, x b ∈ qPilotNormRegion (l := l) T b := by
  simp [globalQPilotRegion]

/-- Actual global containment: the q-pilot product region is inside the global
root hull. -/
theorem globalQPilotRegion_subset_globalRootHull :
    globalQPilotRegion T ⊆ globalRootHull T := by
  intro x hx
  rw [mem_globalQPilotRegion_iff] at hx
  rw [mem_globalRootHull_iff]
  intro b
  exact qPilotNormRegion_subset_rootNormHull (l := l) T b (hx b)

/-- Actual global scalar inequality: the global q-pilot log is at most the
global root hull log, summing the per-b actual inequalities. -/
theorem globalQPilotLog_le_globalRootHullLog
    (mu : ∀ b, Measure (qVFamTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (mu b)] :
    globalQPilotLog (T := T) (mu := mu) ≤ globalRootHullLog (T := T) (mu := mu) := by
  unfold globalQPilotLog globalRootHullLog
  apply Finset.sum_le_sum
  intro b _
  exact qPilotNormLog_le_rootNormHullLog (l := l) T b (mu b)
    (qPilotNormRegion_measure_pos_lt_top (l := l) T b (mu b)).1
    (rootNormHull_measure_lt_top (l := l) T b (mu b))

/-- Actual mixed-prime global data on the fixed product carrier. -/
structure QVFamGlobalProductData where
  productHaar : Measure (QVFamProductCarrier T)
  rootHull : Set (QVFamProductCarrier T)
  qPilotRegion : Set (QVFamProductCarrier T)
  qPilot_subset_rootHull : qPilotRegion ⊆ rootHull
  qPilotLog : Real
  rootHullLog : Real
  qPilotLog_le_rootHullLog : qPilotLog ≤ rootHullLog

/-- The actual mixed-prime global data constructor. -/
noncomputable def qVFamGlobalProductData
    (mu : ∀ b, Measure (qVFamTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (mu b)] :
    QVFamGlobalProductData (l := l) T where
  productHaar := globalProductHaar (T := T) (mu := mu)
  rootHull := globalRootHull T
  qPilotRegion := globalQPilotRegion T
  qPilot_subset_rootHull := globalQPilotRegion_subset_globalRootHull T
  qPilotLog := globalQPilotLog T mu
  rootHullLog := globalRootHullLog T mu
  qPilotLog_le_rootHullLog := globalQPilotLog_le_globalRootHullLog T mu

end LeanFormal.IUT.XiFPaper.QVFamGlobalProductCarrierActual

end
