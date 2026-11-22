import tmp.sheaf.xif.paper.ConcretePaperUnconditionalDataUnconditionalActual
import tmp.sheaf.xif.paper.PaperXiFUnconditional
import tmp.sheaf.xif.paper.ConcreteThetaLinkSourceActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ConcretePaperUnconditionalDataActual
open LeanFormal.IUT.XiFPaper.ConcretePaperUnconditionalDataUnconditionalActual
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.ConcreteSignedHullUnconditionalActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2702PaperConditionalActual

universe ua upi umon ui

/-- Conditional paper 3.12 consumer: from the exact source q-log equality hq and the
exact source comparison hcomp, produce the paper unconditional data (and hence the
paper xi-f inequality).  No additional hypotheses. -/
noncomputable def S2702PaperConditionalData
    {l : PrimeGeFive}
    {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
    {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type} [Fintype iota] {W : iota -> Type}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (nu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure nu]
    (D : SourcePilotRegionDonors I)
    (v : FinitePrimePlace 2 7)
    (hq : concreteQLogIdentification (l := l) (I := I) D)
    (hcomp : concreteSourceComparison (concreteQPilotObject (l := l) (I := I))
      (unconditionalHull (l := l) (I := I) places tuple nu D)) :=
  concretePaperUnconditionalDataUnconditional (l := l) (I := I)
    places tuple nu D v hq hcomp

/-- The induced paper xi-f inequality, with the concrete label-group instance supplied explicitly. -/
theorem S2702PaperConditional_qPilot_le
    {l : PrimeGeFive}
    {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
    {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type} [Fintype iota] {W : iota -> Type}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (nu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure nu]
    (D : SourcePilotRegionDonors I)
    (v : FinitePrimePlace 2 7)
    [Group (ConcreteFiniteTheorem311.finiteLabel l)]
    (hq : concreteQLogIdentification (l := l) (I := I) D)
    (hcomp : concreteSourceComparison (concreteQPilotObject (l := l) (I := I))
      (unconditionalHull (l := l) (I := I) places tuple nu D)) :
    (concreteQPilotObject (l := l) (I := I)).qPilotLogVolume ≤
      (unconditionalHull (l := l) (I := I) places tuple nu D).signedHullLogVolume :=
  (S2702PaperConditionalData places tuple nu D v hq hcomp).qPilot_le_signedHull

end LeanFormal.IUT.XiFPaper.S2702PaperConditionalActual
end