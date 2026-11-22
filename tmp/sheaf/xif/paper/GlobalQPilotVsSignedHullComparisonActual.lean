import tmp.sheaf.xif.paper.ConcreteSignedHullActual
import tmp.sheaf.xif.paper.GlobalQPilotProcessionLogVolumeActual
import tmp.sheaf.xif.paper.SignedAverageBoundActual

/-! # Global q-pilot magnitude versus the unconditional signed hull average

This file compares the actual global q-pilot log-magnitude constructed from the
V_bad base q family (GlobalQPilotProcessionLogVolumeActual) with the actual
procession average of the unconditional concrete PaperSignedHull constructed
from the normalized Haar measure and the Gaussian q = 1/5 source C3.

The actual signed average is

  average = log 5 * (gaussExponentSum / card(SignedLabel l.value)),

while the global q-pilot magnitude is the actual V_bad sum of base q log
magnitudes.  The source comparison is stated explicitly; it is reduced to the
exact arithmetic comparison of these actual quantities.  No inequality is
asserted.  Under the precise obstacle globalQPilotLogMagnitude = log 5 and
coefficient > 1, the comparison is refuted.

No sorry, axiom, True, or PUnit is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.GlobalQPilotVsSignedHullComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.PaperSignedHullSignedActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.ConcreteSignedHullActual
open LeanFormal.IUT.XiFPaper.GlobalQPilotProcessionLogVolumeActual
open LeanFormal.IUT.XiFPaper.SignedAverageBoundActual
open MeasureTheory
open scoped BigOperators

universe ua uv upi umon ui uK uW

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type uv} [Fintype iota] {W : iota -> Type uW}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]

variable (D : SourcePilotRegionDonors (l := l) (V := V) I)
variable (nu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure nu]

variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual unconditional signed hull average (normalized Haar measure). -/
noncomputable def concreteHullAverage : Real :=
  (concretePaperSignedHull (l := l) (V := V) (I := I) places tuple D nu).procession.average

/-- The concrete hull average is the actual Gaussian signed average. -/
theorem concreteHullAverage_eq_gaussian :
    concreteHullAverage (l := l) (V := V) (I := I) places tuple D nu =
      (c3ThetaSignedProcession
        (actualSignedC3 (l := l) (V := V) (I := I) D)).average := by
  unfold concreteHullAverage
  rw [concretePaperSignedHull_procession]

/-- The concrete hull average formula at q = 1/5. -/
theorem concreteHullAverage_eq_log5_mul_sum_div_card :
    concreteHullAverage (l := l) (V := V) (I := I) places tuple D nu =
      Real.log (5 : Real) *
        ((gaussExponentSum (l := l) : Real) /
          (Fintype.card (SignedLabel l.value) : Real)) := by
  rw [concreteHullAverage_eq_gaussian]
  exact actualSignedC3_signedAverage_eq_log5_mul_sum_div_card
    (l := l) (V := V) (I := I) D

/-- The actual source comparison: the signed hull average is at most the
global q-pilot log magnitude. -/
def GlobalQVsSignedHullComparison : Prop :=
  concreteHullAverage (l := l) (V := V) (I := I) places tuple D nu <=
    globalQPilotLogMagnitude T

/-- Exact arithmetic obstacle for the comparison: the global q-pilot magnitude
is log 5 and the theta coefficient is > 1. -/
def GlobalQComparisonObstacle : Prop :=
  globalQPilotLogMagnitude T = Real.log (5 : Real) ∧
    1 < (gaussExponentSum (l := l) : Real) /
      (Fintype.card (SignedLabel l.value) : Real)

/-- The comparison is exactly the arithmetic inequality for the actual
coefficient. -/
theorem globalQVsSignedHullComparison_iff
    (hglobal : globalQPilotLogMagnitude T = Real.log (5 : Real)) :
    GlobalQVsSignedHullComparison (l := l) (V := V) (I := I)
        places tuple D nu T ↔
      (gaussExponentSum (l := l) : Real) /
          (Fintype.card (SignedLabel l.value) : Real) <= 1 := by
  unfold GlobalQVsSignedHullComparison
  rw [concreteHullAverage_eq_log5_mul_sum_div_card (l := l) (V := V) (I := I)
    places tuple D nu, hglobal]
  have hlog : (0 : Real) < Real.log (5 : Real) :=
    Real.log_pos (by norm_num : (1 : Real) < 5)
  constructor
  · intro h
    have h' : Real.log (5 : Real) *
        ((gaussExponentSum (l := l) : Real) /
          (Fintype.card (SignedLabel l.value) : Real)) <=
        Real.log (5 : Real) * 1 := by simpa using h
    exact (mul_le_mul_right hlog).mp h'
  · intro h
    calc
      Real.log (5 : Real) *
          ((gaussExponentSum (l := l) : Real) /
            (Fintype.card (SignedLabel l.value) : Real)) <=
          Real.log (5 : Real) * 1 := by gcongr
      _ = Real.log (5 : Real) := by ring

/-- The precise obstacle refutes the source comparison. -/
theorem not_globalQVsSignedHullComparison_of_obstacle
    (h : GlobalQComparisonObstacle (l := l) T) :
    ¬ GlobalQVsSignedHullComparison (l := l) (V := V) (I := I)
        places tuple D nu T := by
  rcases h with ⟨hglobal, hcoeff⟩
  have hlog : (0 : Real) < Real.log (5 : Real) :=
    Real.log_pos (by norm_num : (1 : Real) < 5)
  unfold GlobalQVsSignedHullComparison
  rw [concreteHullAverage_eq_log5_mul_sum_div_card (l := l) (V := V) (I := I)
    places tuple D nu, hglobal]
  exact not_le_of_gt (mul_lt_mul_of_pos_left hcoeff hlog)

end LeanFormal.IUT.XiFPaper.GlobalQPilotVsSignedHullComparisonActual

end
