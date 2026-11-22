import tmp.sheaf.xif.paper.ConcreteThetaLinkSourceActual
import tmp.sheaf.xif.paper.ConcretePaperSignedHullActual
import tmp.sheaf.xif.paper.NativeTorsionFieldsComplete
import tmp.sheaf.xif.paper.SourceTheaterLogVolumeSign

/-!
# Concrete source comparison: actual reduction and obstruction

The concrete paper q-pilot object has

  O.qPilotLogVolume = sourceQPilotSignedLog I.initial
                    = -sourceBadQAbsLog I.initial,

while the concrete signed hull has procession average equal to the actual
Gaussian signed theta average of the q = 1/5 source theater:

  (c3ThetaSignedProcession actualSignedC3).average.

Thus the concrete comparison

  P.procession.average <= -O.qPilotLogVolume

is actually equivalent to the arithmetic source inequality

  (c3ThetaSignedProcession actualSignedC3).average
    <= sourceBadQAbsLog I.initial.

This reduction is proved below from actual definitions (no fake inequality).
The arithmetic inequality itself is not derived: sourceBadQAbsLog depends on the
bad q-parameters of I.initial, while the signed average depends on the
Gaussian theta values q = 1/5. Under the exact condition
sourceBadQAbsLog = 0 and positive signed average, the comparison is refutable.
No inequality is asserted unconditionally.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.ConcreteSourceComparisonInequalityActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion

universe ua uv upi umon ui uG uL uC uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]

/-- Actual reduction of the concrete source comparison to the source bad-q sum
inequality. -/
theorem concreteSourceComparison_iff_badQAbsLog
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial) :
    concreteSourceComparison O P ↔
      P.procession.average ≤ sourceBadQAbsLog I.initial := by
  unfold concreteSourceComparison
  rw [hO, sourceQPilotSignedLog]
  constructor <;> intro h <;> linarith

/-- Under the concrete q-pilot scalar identification, the comparison is exactly
the bad-q absolute-log bound. -/
theorem concreteSourceComparison_of_badQAbsLog
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial)
    (h : sourceBadQAbsLog I.initial ≥ P.procession.average) :
    concreteSourceComparison O P :=
  (concreteSourceComparison_iff_badQAbsLog O P hO).mpr h

/-- Exact refutation: if the source bad-q absolute log is zero and the signed
hull average is positive, the concrete source comparison is false. -/
theorem not_concreteSourceComparison_of_badQAbsLog_zero
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (hO : O.qPilotLogVolume = sourceQPilotSignedLog I.initial)
    (hzero : sourceBadQAbsLog I.initial = 0)
    (havg : 0 < P.procession.average) :
    ¬ concreteSourceComparison O P := by
  intro h
  have hbound := (concreteSourceComparison_iff_badQAbsLog O P hO).mp h
  linarith

end LeanFormal.IUT.XiFPaper.ConcreteSourceComparisonInequalityActual

end
