import tmp.sheaf.xif.paper.PaperC3ThetaRootActual
import LeanFormal.IUT.Foundations.Theta.OddThetaNormalization

/-!
# P5-A: label-indexed analytic theta shift

ThetaLabel (positive representatives 1..l*) is the label type of the
root-valued paper theta.  This file transports the analytic oddTheta shift
law/normalized evaluation to that label indexing:

  oddTheta q (i * r^j) / oddTheta q i = r^(-(j^2)),

where j is the positive integer representative of the ThetaLabel.  This is a
label-indexed form of the already-proved OddThetaNormalization identity; it
does not assert a bridge to paperRootThetaUnit or a line-bundle section.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1P5LabelShiftActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.Foundations.Theta

variable {L : Type*} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable {l : PrimeGeFive}

/-- The positive integer exponent attached to a ThetaLabel. -/
def thetaLabelExponent (j : ThetaLabel (l := l)) : Int :=
  (thetaLabelToSigned (l := l) j).1

theorem thetaLabelExponent_pos (j : ThetaLabel (l := l)) :
    0 < thetaLabelExponent j := j.2

theorem thetaLabelExponent_injective :
    Function.Injective (thetaLabelExponent (l := l)) := by
  intro a b hab
  apply thetaLabelToSigned_injective (l := l)
  exact Subtype.ext hab

/-- Label-indexed analytic theta point i * r^(j). -/
def analyticThetaLabelPoint (i r : L) (j : ThetaLabel (l := l)) : L :=
  i * r ^ thetaLabelExponent j

/-- Label-indexed normalized oddTheta special value. -/
theorem oddThetaFraction_eval_thetaLabel
    (q r i : L) (hr : r ^ 2 = q) (hr0 : r ≠ 0) (hi : i ^ 2 = -1)
    (hq : ‖q‖ < 1) (hTheta : oddTheta q i ≠ 0) (j : ThetaLabel (l := l)) :
    oddTheta q (analyticThetaLabelPoint i r j) / oddTheta q i =
      r ^ (-(thetaLabelExponent j ^ 2)) := by
  unfold analyticThetaLabelPoint thetaLabelExponent
  exact oddThetaFraction_eval q r i hr hr0 hi hq hTheta
    (thetaLabelToSigned (l := l) j).1

#print axioms oddThetaFraction_eval_thetaLabel
#print axioms thetaLabelExponent_injective

end LeanFormal.IUT.XiFPaper.Mzk1P5LabelShiftActual
