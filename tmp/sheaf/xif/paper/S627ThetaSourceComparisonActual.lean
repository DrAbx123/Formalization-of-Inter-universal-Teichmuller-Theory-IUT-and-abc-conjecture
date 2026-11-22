import tmp.sheaf.xif.paper.ThetaLinkFromSource
import tmp.sheaf.xif.paper.QPilotObjectActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S627ThetaSourceComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ThetaLinkFromSource

universe ua uv upi umon ui uC3 uD3 uM uP uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]

/-- Exact paper xi-f comparison between the actual q-pilot magnitude and the
signed hull procession average. -/
def paperComparisonGap
    (O : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP}
      (l := l) (V := V) (I := I))
    (P : PaperSignedHull X label) : Prop :=
  P.procession.average ≤ O.qPilotLogMagnitude

/-- The ThetaLinkFromSource comparison is exactly the average-vs-q-magnitude
inequality. -/
theorem thetaSourceComparison_iff_gap
    (O : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP}
      (l := l) (V := V) (I := I))
    (P : PaperSignedHull X label) :
    thetaSourceComparison O P ↔ paperComparisonGap O P := by
  unfold thetaSourceComparison paperComparisonGap PaperQPilotObjectActual.qPilotLogMagnitude
  constructor <;> intro h <;> linarith

/-- Construct the paper xi-f comparison from the explicit average/q-magnitude
inequality. This is not a proof of that inequality. -/
theorem thetaSourceComparison_of_gap
    (O : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP}
      (l := l) (V := V) (I := I))
    (P : PaperSignedHull X label)
    (h : paperComparisonGap O P) :
    thetaSourceComparison O P :=
  (thetaSourceComparison_iff_gap O P).mpr h

/-- Exact missing paper xi-f comparison: no inhabitant is provided. -/
def MissingPaperXiFComparison
    (O : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP}
      (l := l) (V := V) (I := I))
    (P : PaperSignedHull X label) : Prop :=
  paperComparisonGap O P

/-- The comparison is not implied by the actual sign facts alone. -/
def PaperXiFComparisonExactGap
    (O : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3, uM, uP}
      (l := l) (V := V) (I := I))
    (P : PaperSignedHull X label) : Prop :=
  MissingPaperXiFComparison O P

end LeanFormal.IUT.XiFPaper.S627ThetaSourceComparisonActual

end
