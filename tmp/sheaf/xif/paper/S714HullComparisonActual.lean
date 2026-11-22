import tmp.sheaf.xif.paper.S663ActualAverageNormalizedHaarActual
import tmp.sheaf.n8.closure.C6ActualIQData
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import Mathlib.MeasureTheory.Group.Measure
import tmp.sheaf.xif.paper.S694ThetaAverageNormalizationActual
import tmp.sheaf.xif.paper.S695QPilotNormalizationAuditActual
import tmp.sheaf.xif.paper.S707ThetaHullVsThetaValueActual
import tmp.sheaf.xif.paper.S657RootSignedHullIndependentActual

/-! # S714: correct hull comparison -|log Theta| <= |log q|

P := s663PaperSignedHull.  By S707,
  thetaPilotMagnitude P = -P.signedHullLogVolume = P.procession.average.
The comparison target is
  P.procession.average <= paperQPilotMagnitude,
where paperQPilotMagnitude is the positive |log q| = order * log p.
S694 supplies the correct paper theta average over l* labels.
No theta-value ratio is used. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S714HullComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.S663ActualAverageNormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S694ThetaAverageNormalizationActual
open LeanFormal.IUT.XiFPaper.S695QPilotNormalizationAuditActual
open LeanFormal.IUT.XiFPaper.S707ThetaHullVsThetaValueActual
open LeanFormal.IUT.XiFPaper.S657RootSignedHullIndependentActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open MeasureTheory

universe u v w
variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type v} [Fintype iota] {W : iota -> Type w}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (nu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure nu]
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Positive qPilot magnitude = classical order/(2l) * log p. -/
noncomputable def paperQPilotMagnitude : Real :=
  (((QPilotZeroLocusDivisorActual.qVFamily T b).order : Real) /
    (2 * (l.value : Real))) * Real.log (qVFamTensorP T b : Real)

/-- Map a positive paper theta label i in {0,...,l*-1} to j=i+1. -/
def paperThetaIndexToSigned (i : PaperThetaLabel l) : SignedLabel l.value :=
  ⟨(i.1 : Int) + 1, by
    have hi := i.2
    have hstar : lStar l.value = (l.value - 1) / 2 := rfl
    constructor
    · have : (0 : Int) ≤ (i.1 : Int) := by exact_mod_cast Nat.zero_le _
      have hnn : (0 : Int) ≤ (lStar l.value : Int) := by exact_mod_cast Nat.zero_le _
      omega
    · have h1 : (i.1 : Int) + 1 ≤ (lStar l.value : Int) := by
        exact_mod_cast Nat.succ_le_of_lt hi
      exact h1⟩

/-- Correct paper theta average over l* positive labels, S694 weights. -/
noncomputable def paperThetaAverage : Real :=
  paperThetaLabelAverage (l := l)
    (fun i : PaperThetaLabel l =>
      rootThetaMagnitudeValue T b (paperThetaIndexToSigned (l := l) i))

/-- S714 hull comparison target: Theta hull magnitude at most qPilot magnitude. -/
def s714HullComparison : Prop :=
  paperThetaAverage (l := l) T b ≤ paperQPilotMagnitude (l := l) T b

/-- Exact missing target datum. -/
def S714HullComparisonRequired : Prop :=
  s714HullComparison (l := l) T b

/-- The S663 hull's theta-pilot magnitude is its procession average. -/
theorem s663ThetaPilotMagnitude_eq_average :
    thetaPilotMagnitude (s663PaperSignedHull (l := l) (K := K) (p := p)
      places tuple nu T b) =
      (s663PaperSignedHull (l := l) (K := K) (p := p)
        places tuple nu T b).procession.average :=
  thetaPilotMagnitude_eq_processionAverage _

/-- Candidate arithmetic ratio for l=29: l*=14, average j^2/(2l) is
    (15*29)/(6*58) > 1.  This indicates the remaining comparison needs the
    full global V_bad/local-degree normalization, not a theta-value ratio. -/
theorem l29_candidateAverageRatio_gt_one :
    (1 : Real) < (15 * 29 : Real) / (6 * 58) := by
  norm_num

end LeanFormal.IUT.XiFPaper.S714HullComparisonActual

end
