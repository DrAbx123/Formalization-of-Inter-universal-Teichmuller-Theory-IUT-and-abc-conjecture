import tmp.sheaf.xif.paper.S2706DirectHcompActual
import tmp.sheaf.xif.paper.S2702PaperConditionalActual
import tmp.sheaf.xif.paper.S2678PaperUnconditionalHcompActual
import tmp.sheaf.xif.paper.ConcreteThetaLinkSourceActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S2706DirectHcompActual
open LeanFormal.IUT.XiFPaper.S2702PaperConditionalActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.ConcretePaperUnconditionalDataActual
open LeanFormal.IUT.XiFPaper.ConcretePaperUnconditionalDataUnconditionalActual
open LeanFormal.IUT.XiFPaper.ConcreteSignedHullUnconditionalActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

/-!
# S2707: conditional paper unconditional data at l = 5

STATUS: CONDITIONAL. This file packages the S2706 direct hcomp and the S2702
conditional consumer. The remaining explicit input is

  hq : concreteQLogIdentification D,

i.e. sourceQPilotSignedLog (S2706I ...).initial = localSignedLog (actualSignedC3 D).q.

For the concrete two-place S1280 data this hq is NOT inhabited: the source
bad-q absolute-log sum and the C3 completion q log have different
normalizations/objects and no bridge exists (ConcreteSourceQIdentification
no-go). Consequently S2707 does not close paper 3.12 and must not be recorded as
an unconditional paper 3.12 proof. No sorry, no axiom, no fake hq.
-/
namespace LeanFormal.IUT.XiFPaper.S2707PaperUnconditionalActual

/-- The S2707 paper unconditional data: I is the S2706 concrete initial input,
P is the unconditional normalized Haar hull, hP is the 2 log 5 procession
identity, hcomp is S2706 direct hcomp, and hq is the explicit q-log input. -/
noncomputable def S2707PaperUnconditional
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type} [Fintype iota] {W : iota -> Type}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (nu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure nu]
    (D : SourcePilotRegionDonors
      (S2706I R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat))
    (v : FinitePrimePlace 2 7)
    (hq : concreteQLogIdentification
      (l := fiveLabel)
      (I := S2706I R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat) D) := by
  let I := S2706I R redCompat hredCompat torCompat htorCompat orbCompat
    horbCompat secCompat hsecCompat cusCompat hcusCompat
  letI : Preorder (ConcreteFiniteTheorem311.ProcessionChoice fiveLabel) :=
    concreteProcessionChoicePreorder fiveLabel
  let P := unconditionalHull (l := fiveLabel) (I := I) places tuple nu D
  have hP : P.procession.average = 2 * Real.log 5 := by
    rw [show P.procession =
      c3ThetaSignedProcession (actualSignedC3 (l := fiveLabel) (V := FinitePrimePlace 2 7) (I := I) D) from
      unconditionalPaperSignedHull_procession_eq (l := fiveLabel) (I := I) places tuple D nu]
    exact signedAverage_eq_two_log5 I D
  have hcomp : concreteSourceComparison
      (paperQPilotObjectConcrete (l := fiveLabel) (I := I)) P := by
    exact S2706_directHcomp R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat P hP
  exact S2702PaperConditionalData (l := fiveLabel) (I := I)
    places tuple nu D v hq hcomp

end LeanFormal.IUT.XiFPaper.S2707PaperUnconditionalActual
end