import tmp.sheaf.xif.paper.ConcreteSourceComparisonActual
import tmp.sheaf.xif.paper.ConcreteSignedHullUnconditionalActual
import tmp.sheaf.xif.paper.PaperSignedHullSignedActual

/-! # S660: exact scalar reduction of ConcreteSourceComparisonObstacle

The actual q-pilot scalar is sourceQPilotSignedLog = -sourceBadQAbsLog.
The unconditional concrete signed hull has procession
c3ThetaSignedProcession, whose average is the negative unsigned theta average.
Thus the target obstacle is equivalent to the scalar inequality

  -(c3ThetaProcession).average <= sourceBadQAbsLog I.initial.

That scalar comparison is the minimal remaining gap; it is not assumed. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.Theorem311Source.S660ConcreteSourceComparisonObstacleActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ConcretePaperXiFInclusionActual
open LeanFormal.IUT.XiFPaper.ConcreteSignedHullUnconditionalActual
open LeanFormal.IUT.XiFPaper.PaperSignedHullSignedActual
open LeanFormal.IUT.XiFPaper.PaperQPilotConcreteActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open MeasureTheory
open scoped BigOperators

universe ua upi umon ui uK uW

variable {l : PrimeGeFive}
variable {I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7)}
variable {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type} [Fintype iota] {W : iota -> Type uW}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (nu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure nu]
variable (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I)

/-- Exact scalar gap: theta average magnitude vs q-pilot bad |log q|. -/
def ConcreteSourceComparisonScalarGap : Prop :=
  -(c3ThetaProcession
      (actualSignedC3 (l := l) (V := FinitePrimePlace 2 7) (I := I) D)).average
    ≤ sourceBadQAbsLog I.initial

/-- The actual obstacle is exactly the scalar gap. -/
theorem concreteSourceComparisonObstacle_iff_scalarGap :
    LeanFormal.IUT.Theorem311Source.ConcreteSourceComparisonActual.ConcreteSourceComparisonObstacle
        (l := l) (I := I)
        (concreteUnconditionalHull (l := l) (I := I) places tuple D nu) ↔
      ConcreteSourceComparisonScalarGap (l := l) (I := I) D := by
  unfold LeanFormal.IUT.Theorem311Source.ConcreteSourceComparisonActual.ConcreteSourceComparisonObstacle
    LeanFormal.IUT.Theorem311Source.ConcreteSourceComparisonActual.concreteSourceComparison
    LeanFormal.IUT.Theorem311Source.ConcreteSourceComparisonActual.concreteQLogVolume
    ConcreteSourceComparisonScalarGap
  rw [paperQPilotObjectConcrete_qPilotLogVolume]
  rw [unconditionalPaperSignedHull_procession_eq]
  rw [c3ThetaSignedProcession_average_eq_neg]
  rw [show sourceQPilotSignedLog I.initial = -sourceBadQAbsLog I.initial from rfl]
  constructor <;> intro h <;> linarith

/-- Conditional final obstacle from the scalar gap. -/
theorem concreteSourceComparisonObstacle_of_scalarGap
    (h : ConcreteSourceComparisonScalarGap (l := l) (I := I) D) :
    LeanFormal.IUT.Theorem311Source.ConcreteSourceComparisonActual.ConcreteSourceComparisonObstacle
      (l := l) (I := I)
      (concreteUnconditionalHull (l := l) (I := I) places tuple D nu) :=
  (concreteSourceComparisonObstacle_iff_scalarGap (l := l) (I := I)
    places tuple nu D).mpr h

/-- Exact minimal missing scalar comparison. -/
def ConcreteSourceComparisonScalarGapRequired : Prop :=
  ConcreteSourceComparisonScalarGap (l := l) (I := I) D

end LeanFormal.IUT.Theorem311Source.S660ConcreteSourceComparisonObstacleActualAdapted

end
