import tmp.sheaf.xif.paper.S660ConcreteSourceComparisonObstacleActualAdapted
import tmp.sheaf.xif.paper.ConcretePaperXiFInclusionActualAdapted

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S625FinalConditionalPackageActualAdapted
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ConcretePaperXiFInclusionActualAdapted
open LeanFormal.IUT.XiFPaper.ConcreteSignedHullUnconditionalActual
open LeanFormal.IUT.XiFPaper.PaperSignedHullSignedActual
open LeanFormal.IUT.XiFPaper.PaperQPilotConcreteActual
open LeanFormal.IUT.Theorem311Source.S660ConcreteSourceComparisonObstacleActualAdapted
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
variable (v : FinitePrimePlace 2 7)

structure FinalConcreteComparisonPackage where
  hq : (concreteQPilotObject (l := l) I).qPilotLogVolume =
    paperQPilotLogVolume (concreteC3 (l := l) (I := I) D)
  sourcePos : 0 < sourceBadQAbsLog I.initial
  numeric : ConcreteSourceComparisonScalarGap (l := l) (I := I) D
  obstacle :
    LeanFormal.IUT.Theorem311Source.ConcreteSourceComparisonActual.ConcreteSourceComparisonObstacle
      (l := l) (I := I)
      (concreteUnconditionalHull (l := l) (I := I) places tuple D nu)
  inclusion : PaperXiFInclusion (concreteQPilotObject (l := l) I)
    (concreteUnconditionalHull (l := l) (I := I) places tuple D nu)
    (concreteC3 (l := l) (I := I) D)

noncomputable def finalConcreteComparisonPackage
    (hq : (concreteQPilotObject (l := l) I).qPilotLogVolume =
      paperQPilotLogVolume (concreteC3 (l := l) (I := I) D))
    (hpos : 0 < sourceBadQAbsLog I.initial)
    (hnumeric : ConcreteSourceComparisonScalarGap (l := l) (I := I) D) :
    FinalConcreteComparisonPackage (l := l) (I := I) places tuple nu D where
  hq := hq
  sourcePos := hpos
  numeric := hnumeric
  obstacle := concreteSourceComparisonObstacle_of_scalarGap (l := l) (I := I)
    places tuple nu D hnumeric
  inclusion := concretePaperXiFInclusion (l := l) (I := I) places tuple D nu hq
    (by
      change LeanFormal.IUT.Theorem311Source.ConcreteSourceComparisonActual.ConcreteSourceComparisonObstacle
        (l := l) (I := I)
        (concreteUnconditionalHull (l := l) (I := I) places tuple D nu)
      exact concreteSourceComparisonObstacle_of_scalarGap (l := l) (I := I)
        places tuple nu D hnumeric)

end LeanFormal.IUT.XiFPaper.S625FinalConditionalPackageActualAdapted
end
