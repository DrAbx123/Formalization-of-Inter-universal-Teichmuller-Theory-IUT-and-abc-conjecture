import tmp.sheaf.xif.paper.Mzk1ProcessionContributionNumericsActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S3137 q/Theta comparison: procession average arithmetic

Uses the proved Unit L average `(1/l*) sum_j j^2*m/(2l)*log p =
((l*+1)/12)*m*log p` (Mzk1ProcessionContributionNumericsActual) to
isolate the real-arithmetic content of the S3137 named comparison.
The equality of the actual Haar hull log-volume with the procession average is
an explicit named proportionality input; it is not proved here. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1S3137ComparisonArithmeticActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ProcessionContributionNumericsActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open scoped BigOperators

/-- Procession-normalized average coefficient `(l*+1)/12 * m * log p`. -/
def processionAverage (m n : Nat) (p : Real) : Real :=
  (((n : Real) + 1) / 12) * (m : Real) * Real.log p

theorem processionAverage_eq_sum (m n : Nat) (p : Real) (hn : 0 < n) :
    (1 / (n : Real)) *
        (∑ j ∈ Finset.range (n + 1),
          processionContribution m (2 * n + 1) j p) =
      processionAverage m n p :=
  processionContribution_average m n p hn

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))
variable (m n : Nat) (p : Real)

/-- Named proportionality: the actual Haar hull log-volume equals the procession
average.  This is an explicit input, not a consequence of the definitions. -/
def ThetaHullProportionalToProcession : Prop :=
  thetaPilotHullLogVolumeReal C3 = processionAverage m n p

/-- The q-pilot arithmetic value used in the comparison: `-m log p/(2(2l*+1))`. -/
def qPilotArithmeticVolume : Real :=
  -((m : Real) * Real.log p / (2 * ((2 * n + 1 : Nat) : Real)))

/-- Reduction of the S3137 named comparison to pure real arithmetic, given
the proportionality and the q normalization. -/
theorem qThetaComparison_iff_arithmetic
    (hTheta : thetaPilotHullLogVolumeReal C3 = processionAverage m n p)
    (hq : qPilotLogVolumeReading P = qPilotArithmeticVolume m n p) :
    qThetaPilotLogVolumeComparison C3 P ↔
      qPilotArithmeticVolume m n p ≤ processionAverage m n p := by
  unfold qThetaPilotLogVolumeComparison
  rw [hTheta, hq]
  exact Iff.rfl

/-- Numeric instance (l=13 => l*=6, p=11, m=5): the arithmetic inequality holds. -/
theorem numeric_l13_p11_m5 :
    qPilotArithmeticVolume 5 6 11 ≤ processionAverage 5 6 11 := by
  unfold qPilotArithmeticVolume processionAverage
  have hlog : 0 ≤ Real.log (11 : Real) := by
    exact Real.log_nonneg (by norm_num)
  norm_num
  nlinarith [hlog]

end LeanFormal.IUT.XiFPaper.Mzk1S3137ComparisonArithmeticActual

end
