import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.NativeQVPilotNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedIntegers
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# S22: dependent-p product carrier and per-b qVFamily bridge

The dependent-p carrier is

  (b : Bad (nativePlaceSelection T)) ->
    Completion ((nativeBadLift T).lift b),

with one full completion factor per bad place and its own rational prime p_b.
It is not a single ArithmeticTensorTupleBlock.

This file constructs the actual product carrier, the actual product point
determined by qVFamily, the family of per-b projections, and the actual weighted
qVFamily log-magnitude

  sum_b nativeBadLocalWeight T b * (-log ||qVFamily T b||).

The weighted product magnitude is proved equal to the native normalized
qVFamily magnitude.  The product Haar measure is not constructed here: the bare
dependent completion product has no supplied measurable/locally compact product
structure, so a Haar measure is not fabricated.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S22DependentProductActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The dependent completion at a bad place. -/
abbrev DependentCompletion (b : Bad (nativePlaceSelection T)) : Type :=
  Completion ((nativeBadLift T).lift b)

noncomputable instance dependentCompletionMeasurableSpace
    (b : Bad (nativePlaceSelection T)) :
    MeasurableSpace (DependentCompletion T b) :=
  borel (DependentCompletion T b)

noncomputable instance dependentCompletionBorelSpace
    (b : Bad (nativePlaceSelection T)) :
    BorelSpace (DependentCompletion T b) :=
  ⟨rfl⟩

noncomputable instance dependentCompletionLocallyCompactSpace
    (b : Bad (nativePlaceSelection T)) :
    LocallyCompactSpace (DependentCompletion T b) :=
  (normalizedCompletionHomeomorph ((nativeBadLift T).lift b)).locallyCompactSpace_iff.mp
    inferInstance



/-- The actual dependent-p product carrier: one full completion per bad place. -/
abbrev DependentCompletionProduct : Type :=
  (b : Bad (nativePlaceSelection T)) -> DependentCompletion T b

/-- The actual product Haar measure on the dependent-p carrier. -/
noncomputable def dependentCompletionHaar :
    Measure (DependentCompletionProduct T) :=
  Measure.pi (fun b : Bad (nativePlaceSelection T) =>
    (Measure.addHaar : Measure (DependentCompletion T b)))

/-- The actual Haar mu_log of a product region. -/
noncomputable def dependentCompletionMuLog
    (S : Set (DependentCompletionProduct T)) : ENNReal :=
  haarLogVolume (dependentCompletionHaar T) S

/-- The actual product unit region: product of the unit balls. -/
def dependentCompletionUnitRegion :
    Set (DependentCompletionProduct T) :=
  Set.pi Set.univ (fun b : Bad (nativePlaceSelection T) =>
    Metric.closedBall (0 : DependentCompletion T b) 1)

/-- Per-b product ball region with arbitrary actual radii. -/
def dependentCompletionBallRegion
    (r : Bad (nativePlaceSelection T) -> Real) :
    Set (DependentCompletionProduct T) :=
  Set.pi Set.univ (fun b =>
    Metric.closedBall (0 : DependentCompletion T b) (r b))

/-- Product measure of a per-b ball region is the product of the local ball
measures. -/
theorem dependentCompletionBallRegion_measure
    (r : Bad (nativePlaceSelection T) -> Real) :
    dependentCompletionHaar T (dependentCompletionBallRegion T r) =
      ∏ b : Bad (nativePlaceSelection T),
        (Measure.addHaar : Measure (DependentCompletion T b))
          (Metric.closedBall (0 : DependentCompletion T b) (r b)) := by
  unfold dependentCompletionBallRegion dependentCompletionHaar
  rw [Measure.pi_pi]

/-- The actual product point determined by the qVFamily q candidates. -/
noncomputable def dependentQVFamProductPoint :
    DependentCompletionProduct T :=
  fun b => (qVFamily T b).q

/-- Projection to the bad-place component. -/
def dependentProductProjection
    (b : Bad (nativePlaceSelection T)) :
    DependentCompletionProduct T -> DependentCompletion T b :=
  fun x => x b

/-- The qVFamily product point projects to qVFamily q at b. -/
theorem dependentQVFamProductPoint_apply
    (b : Bad (nativePlaceSelection T)) :
    dependentProductProjection T b (dependentQVFamProductPoint T) =
      (qVFamily T b).q :=
  rfl


/-- The unit region is the ball region with all radii one. -/
theorem dependentCompletionUnitRegion_eq_ball :
    dependentCompletionUnitRegion T =
      dependentCompletionBallRegion T (fun _ => 1) :=
  rfl

/-- Product measure of the unit region is the product of the local unit-ball
measures. -/
theorem dependentCompletionUnitRegion_measure :
    dependentCompletionHaar T (dependentCompletionUnitRegion T) =
      ∏ b : Bad (nativePlaceSelection T),
        (Measure.addHaar : Measure (DependentCompletion T b))
          (Metric.closedBall (0 : DependentCompletion T b) 1) := by
  rw [dependentCompletionUnitRegion_eq_ball, dependentCompletionBallRegion_measure]

/-- Product mu_log of the unit region is the Haar log-volume of its product
measure. -/
theorem dependentCompletionUnitRegion_muLog :
    dependentCompletionMuLog T (dependentCompletionUnitRegion T) =
      haarLogVolume (dependentCompletionHaar T)
        (dependentCompletionUnitRegion T) :=
  rfl


/-- The product unit-region measure is positive. -/
theorem dependentCompletionUnitRegion_measure_pos :
    0 < dependentCompletionHaar T (dependentCompletionUnitRegion T) := by
  rw [dependentCompletionUnitRegion_measure]
  apply bot_lt_iff_ne_bot.mpr
  change (∏ b : Bad (nativePlaceSelection T),
    (Measure.addHaar : Measure (DependentCompletion T b))
      (Metric.closedBall (0 : DependentCompletion T b) 1)) ≠ (0 : ENNReal)
  rw [Finset.prod_ne_zero_iff]
  intro b _
  exact (Metric.measure_closedBall_pos
    (Measure.addHaar : Measure (DependentCompletion T b)) 0 one_pos).ne'

/-- Exact missing input: a ProperSpace instance on each raw completion. -/
def DependentCompletionProperSpaceMissing : Prop :=
  ∀ b : Bad (nativePlaceSelection T), Nonempty (ProperSpace (DependentCompletion T b))

/-- Under the exact ProperSpace input, the product unit-region measure is finite. -/
theorem dependentCompletionUnitRegion_measure_lt_top_of_proper
    (hproper : DependentCompletionProperSpaceMissing (l := l) T) :
    dependentCompletionHaar T (dependentCompletionUnitRegion T) < ⊤ := by
  rw [dependentCompletionUnitRegion_measure]
  apply ENNReal.prod_lt_top
  intro b _
  letI : ProperSpace (DependentCompletion T b) := Classical.choice (hproper b)
  exact MeasureTheory.measure_closedBall_lt_top
    (μ := (Measure.addHaar : Measure (DependentCompletion T b))) (x := 0) (r := 1)


/-- Minimal exact API for finiteness: compactness of each local closed unit ball.
This is weaker than a global ProperSpace instance and is the only missing input. -/
def DependentCompletionClosedBallCompactMissing : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    IsCompact (Metric.closedBall (0 : DependentCompletion T b) 1)

/-- Conditional finiteness of the product unit-region measure from the minimal
closed-ball compactness API. -/
theorem dependentCompletionUnitRegion_measure_lt_top_of_closedBallCompact
    (hcompact : DependentCompletionClosedBallCompactMissing (l := l) T) :
    dependentCompletionHaar T (dependentCompletionUnitRegion T) < ⊤ := by
  rw [dependentCompletionUnitRegion_measure]
  apply ENNReal.prod_lt_top
  intro b _
  exact (hcompact b).measure_lt_top


/-- Actual compactness of the raw completion closed unit ball, transferred from
the normalized completion via the actual ring equivalence and its unit-ball
comparison. -/
theorem dependentCompletion_closedUnitBall_compact
    (b : Bad (nativePlaceSelection T)) :
    IsCompact (Metric.closedBall (0 : DependentCompletion T b) 1) := by
  let e := normalizedCompletionRingEquiv ((nativeBadLift T).lift b)
  have hnorm : IsCompact
      (Metric.closedBall (0 : NormalizedCompletion ((nativeBadLift T).lift b)) 1) :=
    isCompact_closedBall 0 1
  have himg : IsCompact
      (e '' Metric.closedBall
        (0 : NormalizedCompletion ((nativeBadLift T).lift b)) 1) :=
    hnorm.image (normalizedCompletionHomeomorph ((nativeBadLift T).lift b)).continuous
  convert himg using 1
  ext x
  simp only [Set.mem_image, Metric.mem_closedBall, dist_eq_norm, sub_zero]
  constructor
  · intro hx
    refine ⟨e.symm x, ?_, ?_⟩
    · apply (normalizedCompletion_norm_le_one_iff
        ((nativeBadLift T).lift b) (e.symm x)).mp
      simpa [e] using hx
    · simp
  · rintro ⟨y, hy, rfl⟩
    exact (normalizedCompletion_norm_le_one_iff ((nativeBadLift T).lift b) y).mpr hy

/-- The minimal compactness API is actual. -/
theorem dependentCompletionClosedBallCompactMissing_holds :
    DependentCompletionClosedBallCompactMissing (l := l) T :=
  fun b => dependentCompletion_closedUnitBall_compact T b

/-- Unconditional finiteness of the product unit-region measure. -/
theorem dependentCompletionUnitRegion_measure_lt_top :
    dependentCompletionHaar T (dependentCompletionUnitRegion T) < ⊤ := by
  rw [dependentCompletionUnitRegion_measure]
  apply ENNReal.prod_lt_top
  intro b _
  exact (dependentCompletion_closedUnitBall_compact T b).measure_lt_top

/-- The actual log-volume of the product unit region. -/
noncomputable def dependentCompletionUnitLogVolume : Real :=
  (dependentCompletionMuLog T (dependentCompletionUnitRegion T)).toReal

/-- Normalized product mu_log: subtract the unit-region log-volume. -/
noncomputable def dependentCompletionNormalizedMuLog
    (S : Set (DependentCompletionProduct T)) : Real :=
  (dependentCompletionMuLog T S).toReal -
    dependentCompletionUnitLogVolume T

/-- The normalized mu_log of the unit region is zero. -/
theorem dependentCompletionNormalizedMuLog_unitRegion :
    dependentCompletionNormalizedMuLog T
      (dependentCompletionUnitRegion T) = 0 := by
  unfold dependentCompletionNormalizedMuLog dependentCompletionUnitLogVolume
  ring

/-- The unit region is the ball region with all radii one. -/
theorem dependentCompletionMuLog_unitRegion_eq_ballRegion :
    dependentCompletionMuLog T (dependentCompletionUnitRegion T) =
      dependentCompletionMuLog T
        (dependentCompletionBallRegion T (fun _ => 1)) :=
  rfl

/-- Normalized mu_log of the all-one product ball region is zero. -/
theorem dependentCompletionNormalizedMuLog_ballRegion_one :
    dependentCompletionNormalizedMuLog T
      (dependentCompletionBallRegion T (fun _ => 1)) = 0 := by
  unfold dependentCompletionNormalizedMuLog dependentCompletionUnitLogVolume
  rw [← dependentCompletionMuLog_unitRegion_eq_ballRegion]
  ring
/-- The actual weighted per-b qVFamily log-magnitude on the product carrier. -/
noncomputable def dependentQVFamWeightedLogMagnitude : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      (-Real.log ‖dependentProductProjection T b
        (dependentQVFamProductPoint T)‖)

/-- The weighted product qVFamily magnitude is the native normalized qVFamily
magnitude. -/
theorem dependentQVFamWeightedLogMagnitude_eq :
    dependentQVFamWeightedLogMagnitude T =
      nativeQVPilotNormalizedLogMagnitude T := by
  unfold dependentQVFamWeightedLogMagnitude
    nativeQVPilotNormalizedLogMagnitude nativeQVPilotLocalMagnitude
    dependentProductProjection dependentQVFamProductPoint
  simp only [ArithmeticQPilotLogVolume.localLogMagnitude,
    ArithmeticQPilotLogVolume.localSignedLog]

/-- The product carrier is not a single tensor block: it is an actual dependent
function over the bad index. -/
theorem dependentProduct_carrier_eq :
    DependentCompletionProduct T =
      ((b : Bad (nativePlaceSelection T)) -> Completion ((nativeBadLift T).lift b)) :=
  rfl

end LeanFormal.IUT.XiFPaper.S22DependentProductActual

end
