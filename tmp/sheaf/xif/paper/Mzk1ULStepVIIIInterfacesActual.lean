/- U-C: interface signatures for the final StepVIII letter obligations (ruling B).

These are INTERFACE DEFINITIONS (Prop shapes), not proofs: the actual statements
the final chain consumes, with the paper-faithful v2 letters.  david/kurt provide
the corresponding theorems; when their exact names land the consumers switch from
these Props to their proofs.

check list: logDifferentK / SAr_tripodal / dMod (Mzk1ULPaperLettersActual),
sQPaper (Mzk1ULSQPaperActual), kappa/cL (Mzk1UCC3Actual), paperLstarLogs
(Mzk1ULHpktActual), M_paper_v2 / qPilotMagnitudePaper_v2 (Mzk1ULQPilotMagnitudeV2Actual).
-/
import tmp.sheaf.xif.paper.Mzk1ULPaperLettersActual
import tmp.sheaf.xif.paper.Mzk1ULSQPaperActual
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual
import tmp.sheaf.xif.paper.Mzk1UCC3Actual
import tmp.sheaf.xif.paper.Mzk1ULHpktActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULStepVIIIInterfacesActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- INTERFACE: paper Step (ii) with the paper-faithful letters (lambda weights),
log d_K <= S_ar + 2 log l + 21 (IUT IV L1412-1426; the +21 absorbs F vs F_tpd). -/
def hlogK_lambda : Prop :=
  Real.log (NumberField.rootDiscr T.arithmetic.K)
    ≤ SAr_tripodal T + 2 * Real.log (l.value : ℝ) + 21

/-- INTERFACE: paper Step (iii) s^Q estimate with the paper-faithful letters,
log s^Q <= 2 d_mod S_ar + 5 + log l (IUT IV L1553-1575; sQPaper primorial L1436-1501). -/
def hsQ_lambda : Prop :=
  Real.log (sQPaper T)
    ≤ 2 * (Module.finrank ℚ T.arithmetic.Fmod : ℝ) * SAr_tripodal T
      + 5 + Real.log (l.value : ℝ)

/-- INTERFACE: the Step(viii) display with lambda/d_mod outer weights (ruling B):
Sum_b w_b B_b <= kappa ((1+12 d/l) S_ar + 2 log l + 56 - cL(l) Q + (20/3) lstar) - M,
where Q = qPilotMagnitudePaper_v2 / M = M_paper_v2 and w is the lambda/d_mod weight. -/
def hstepVIII_lambdaWeights (w B : Bad (nativePlaceSelection T) → ℝ) : Prop :=
  (∑ b : Bad (nativePlaceSelection T), w b * B b)
    ≤ LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.kappa (l.value : ℝ) *
        ((1 + 12 * (Module.finrank ℚ T.arithmetic.Fmod : ℝ) / (l.value : ℝ))
          * SAr_tripodal T + 2 * Real.log (l.value : ℝ) + 56
          - LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.cL (l.value : ℝ)
            * qPilotMagnitudePaper_v2 (l := l) T
          + (20 / 3) * LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperLstarLogs
              (Module.finrank ℚ T.arithmetic.Fmod) (l.value : ℝ))
      - M_paper_v2 (l := l) T

end LeanFormal.IUT.XiFPaper.Mzk1ULStepVIIIInterfacesActual
end
