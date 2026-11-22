import tmp.sheaf.xif.paper.ConcreteSourceComparisonInequalityActual
import tmp.sheaf.xif.paper.SignedAverageBoundActual

/-!
# Concrete source comparison: numeric reduction and exact obstruction

The actual concrete signed theta average at the Gaussian q = 1/5 source theater
is

  c3ThetaSignedProcession.average
    = log(5) * (gaussExponentSum / card(SignedLabel l.value)),

while the concrete q-pilot scalar is

  qPilotLogVolume = sourceQPilotSignedLog I.initial
                  = -sourceBadQAbsLog I.initial.

Therefore the concrete source comparison is exactly the numeric inequality

  log(5) * (gaussExponentSum / card) <= sourceBadQAbsLog I.initial.

This equivalence is proved below from actual formulas. The inequality itself is
not asserted: sourceBadQAbsLog depends on the actual source bad q-parameters of
I.initial, which are not numerically fixed by the Gaussian q = 1/5 data. Under
an exact zero bad-q hypothesis and positive theta average, the comparison is
refuted.

No fake inequality, True/PUnit, axiom, or sorry is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.ConcreteSourceComparisonNumericActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.ConcreteSourceComparisonInequalityActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion

universe ua uv upi umon ui uG uL uC uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]

/-- The exact numeric theta average formula for the concrete q = 1/5 Gaussian
signed procession. -/
theorem concreteThetaAverage_eq_log5_mul_gaussSum_div_card
    (D : SourcePilotRegionDonors (l := l) (V := V) I) :
    (c3ThetaSignedProcession
        (actualSignedC3 (l := l) (V := V) (I := I) D)).average =
      Real.log (5 : Real) *
        ((gaussExponentSum (l := l) : Real) /
          (Fintype.card (SignedLabel l.value) : Real)) :=
  actualSignedC3_signedAverage_eq_log5_mul_sum_div_card (l := l) (V := V) (I := I) D

/-- The concrete source comparison is exactly the numeric inequality between
the Gaussian theta average and the source bad-q absolute log. -/
theorem concreteComparison_iff_thetaAverage_le_badQAbsLog
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial) :
    concreteSourceComparison O P ↔
      P.procession.average ≤ sourceBadQAbsLog I.initial :=
  concreteSourceComparison_iff_badQAbsLog O P hO

/-- For the actual concrete Gaussian signed hull, the numeric comparison is
exactly the Gauss-sum / bad-q inequality. -/
theorem concreteComparison_iff_gaussSum_le_badQAbsLog
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (D : SourcePilotRegionDonors (l := l) (V := V) I)
    (P : PaperSignedHull (X := X) label)
    (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial)
    (hP : P.procession.average =
      (c3ThetaSignedProcession
        (actualSignedC3 (l := l) (V := V) (I := I) D)).average) :
    concreteSourceComparison O P ↔
      Real.log (5 : Real) *
          ((gaussExponentSum (l := l) : Real) /
            (Fintype.card (SignedLabel l.value) : Real)) ≤
        sourceBadQAbsLog I.initial := by
  rw [concreteComparison_iff_thetaAverage_le_badQAbsLog O P hO, hP,
    concreteThetaAverage_eq_log5_mul_gaussSum_div_card]

/-- Exact refutation under zero source bad-q log and positive signed average. -/
theorem not_concreteComparison_of_zero_badQAbsLog
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial)
    (hzero : sourceBadQAbsLog I.initial = 0)
    (havg : 0 < P.procession.average) :
    ¬ concreteSourceComparison O P :=
  not_concreteSourceComparison_of_badQAbsLog_zero O P hO hzero havg

/-- Exact numeric obstruction: the comparison is exactly an inequality between
the q = 1/5 Gauss average and the actual source bad-q sum; the latter is not
numerically fixed in the tree. This proposition records that exact remaining
inequality without asserting it. -/
def ConcreteNumericSourceObstruction
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (D : SourcePilotRegionDonors (l := l) (V := V) I) : Prop :=
  Real.log (5 : Real) *
      ((gaussExponentSum (l := l) : Real) /
        (Fintype.card (SignedLabel l.value) : Real)) ≤
    sourceBadQAbsLog I.initial

end LeanFormal.IUT.XiFPaper.ConcreteSourceComparisonNumericActual

end
