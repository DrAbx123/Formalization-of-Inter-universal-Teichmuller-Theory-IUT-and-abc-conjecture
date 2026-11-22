import tmp.sheaf.xif.paper.S1122ProductSourceComparisonActual
import tmp.sheaf.xif.paper.S916PaperMultiradialSActual

/-! # S1146: geometric R⊆S route to concreteSourceComparison

Read: ConcreteSourceComparisonActual, ConcreteSourceComparisonInequalityActual,
S1129, S916.

Actual: concreteSourceComparison is equivalent to the q_v-product inequality
  P.procession.average ≤ sourceBadQAbsLog I.initial
(S1122/S1129).  The multiradial hull S = closure(theta images ∪ Ind images) has
actual containment from the model hull R, but there is no actual identification
of P.average with the R log-volume, nor of -qLog with the S log-volume.

Moreover S1122 proves the comparison is FALSE for one allowed bad q close to 1.
Thus an unconditional direct geometric proof is impossible; the exact geometric
log inequality is S1122ProductComparison.  This file reports that exact status
without fake inequality. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1146GeometricComparisonAuditActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.S1122ProductSourceComparisonActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open MeasureTheory

universe ua uv upi umon ui uG uL uC uX uLabel
variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)
variable (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
variable (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial)

/-- Exact geometric log inequality on R and S. -/
def S1146RSubsetSLogInequality : Prop :=
  P.procession.average ≤ sourceBadQAbsLog I.initial

/-- The geometric log inequality is exactly concreteSourceComparison. -/
theorem s1146Geometric_iff_concrete
    (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial) :
    S1146RSubsetSLogInequality (l := l) (I := I) P ↔
      concreteSourceComparison O P :=
  (s1122ConcreteComparison_iff_product O P hO).symm.trans
    (by rfl : S1146RSubsetSLogInequality (l := l) (I := I) P ↔
      S1122ProductComparison (l := l) (I := I) P)

/-- Exact refutation of the unconditional geometric route. -/
theorem s1146_not_unconditional_one_q_close
    (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial)
    (hPavg : P.procession.average = Real.log (25 : Real))
    (hsource : sourceBadQAbsLog I.initial = Real.log ((25 : Real) / 24)) :
    ¬ concreteSourceComparison O P :=
  s1122ProductComparison_false_one_q_close O P hO hPavg hsource

/-- Exact remaining inequality. -/
def S1146ExactMinimum : Prop :=
  S1146RSubsetSLogInequality (l := l) (I := I) P

end LeanFormal.IUT.XiFPaper.S1146GeometricComparisonAuditActualAdapted

end
