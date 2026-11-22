import tmp.sheaf.xif.paper.ConcreteSignedHullUnconditionalActual
import tmp.sheaf.xif.paper.GlobalQVFamThetaHullScalarActual
import tmp.sheaf.xif.paper.GlobalThetaHullVsQPilotComparisonActual

/-! # S1113: ConcreteFinalScalarBridge

There is no file named UnconditionalHullVsFinalScalarAudit or
ConcreteFinalScalarBridge in the tree.  The existing actual pieces are:

* ConcreteSignedHullUnconditionalActual.unconditionalPaperSignedHull_hull_logVolume_eq:
    the C6 hull log-volume of the unconditional concrete signed hull equals
    ENNReal.ofReal (c3ThetaSignedProcession C3).average;
* GlobalQVFamThetaHullScalarActual.globalQVFamQPilotLog:
    the qVFamily q-pilot scalar (weighted sum of local normalized volumes);
* GlobalThetaHullVsQPilotComparisonActual: the global hull-vs-qPilot signed
    comparison card (exact condition, no asserted inequality).

The procession/hull component is actual.  The qPilot-scalar identification
  I.qPilotSignedLogVolume = globalQVFamQPilotLog T
is the exact remaining bridge. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1113ConcreteFinalScalarBridgeActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ConcreteSignedHullUnconditionalActual
open LeanFormal.IUT.XiFPaper.GlobalQVFamThetaHullScalarActual
open LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual
open MeasureTheory

universe ua uv upi umon ui uK uW u

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type uv} [Fintype iota] {W : iota -> Type uW}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (D : SourcePilotRegionDonors (l := l) (V := V) I)
variable (nu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure nu]

/-- Actual concrete procession/hull component: the C6 hull log-volume is the
ofReal of the concrete signed procession average. -/
theorem s1113ConcreteProcessionAverage_eq_hullLogVolume :
    (C6ActualIQData.actual places tuple
        (normalizedHaarMeasure (l := l) (V := V) (I := I)
          places tuple D nu)).iqInterface.logVolume
        (C6ActualIQData.actual places tuple
          (normalizedHaarMeasure (l := l) (V := V) (I := I)
            places tuple D nu)).iqInterface.hull =
      ENNReal.ofReal
        (c3ThetaSignedProcession
          (actualSignedC3 (l := l) (V := V) (I := I) D)).average :=
  unconditionalPaperSignedHull_hull_logVolume_eq
    (l := l) (V := V) (I := I) places tuple D nu

/-- Exact qPilot-scalar identification: the source qPilot scalar equals the
qVFamily global qPilot scalar. -/
def S1113QPilotScalarIdentification : Prop :=
  I.qPilotSignedLogVolume =
    globalQVFamQPilotLog (l := l) T

/-- Exact required bridge. -/
def ConcreteFinalScalarBridgeRequired : Prop :=
  S1113QPilotScalarIdentification (l := l) (I := I) T

end LeanFormal.IUT.XiFPaper.S1113ConcreteFinalScalarBridgeActualAdapted

end
