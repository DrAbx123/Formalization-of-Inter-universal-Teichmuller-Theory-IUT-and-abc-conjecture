import tmp.sheaf.xif.paper.S800LeastLambdaOHullActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual
import Mathlib.Tactic

/-!
# Mzk1PaperTargetNormalizationActual

P0-fix interface for the paper q-root normalization.

The green chain uses c_norm = order(q) (RootNormalizedContainmentActual:83,
RootHullContainmentInequalityActual:111-114).  The paper q-pilot object uses
q_v := q^(1/2l) (IUT I Ex 3.2(iv); IUT III Def 3.8(i)), so its coefficient is
c_root = order(q)/(2l) (S800:76-88; QVFamRootFactorCorrectionActual:56-57).

This file does not remove or rewrite the old c_norm statements.  It packages
the paper-faithful block-level target with c_root on BOTH sides:

  qPilotPaperRegionLog <= paperHullLog

and records the deviation identity c_norm = (2l) * c_root.

The target below is conditional on the explicit positivity/finiteness of the
two measure arguments, as in the existing S800 theorem.  It is not claimed
unconditional; no new hypothesis is hidden in a structure field.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperTargetNormalizationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.S800LeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock T b)]
variable [BorelSpace (qVFamTensorBlock T b)]
variable (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]

/-- c_norm = order(q) (green chain coefficient). -/
noncomputable def cNorm (i : qVFamTensorV) : Real :=
  rootNormCoefficient (l := l) T b i

/-- c_root = order(q)/(2l) (paper q_v coefficient). -/
noncomputable def cRoot (i : qVFamTensorV) : Real :=
  rootHalfCoefficient (l := l) T b i

/-- Paper q-pilot region log (paper half coefficient, no Ind3 c_norm). -/
noncomputable def paperQLog : Real :=
  qPilotPaperRegionLog (l := l) T b mu

/-- Paper Theta-hull log (paper half coefficient, least lambda-O hull). -/
noncomputable def paperThetaLog : Real :=
  paperHullLog (l := l) T b mu

/-- The paper-faithful block target: -|log q| <= -|log Theta|, both read with
c_root = order/(2l). -/
def PaperTargetNormalization : Prop :=
  paperQLog (l := l) T b mu <= paperThetaLog (l := l) T b mu

/-- Conditional proof from the existing S800 comparison.  Positivity and
finiteness of the paper regions are explicit hypotheses, not new target
assumptions. -/
theorem paperTargetNormalization_of_pos_fin
    (hpos : 0 < mu (qPilotPaperRegion (l := l) T b))
    (hfin : mu (leastLambdaOHull (l := l) T b
      (paperPossibleImages (l := l) T b)) < ⊤) :
    PaperTargetNormalization (l := l) T b mu := by
  unfold PaperTargetNormalization paperQLog paperThetaLog
  exact qPilotPaperRegionLog_le_paperHullLog (l := l) T b mu hpos hfin


/-- Paper q-pilot absolute log magnitude A_paper = -paperQLog. -/
noncomputable def paperA : Real := -paperQLog (l := l) T b mu

/-- Paper Theta-hull absolute log magnitude R_paper = -paperThetaLog. -/
noncomputable def paperR : Real := -paperThetaLog (l := l) T b mu

/-- Paper target difference M_paper = A_paper - R_paper. -/
noncomputable def paperM : Real := paperA (l := l) T b mu - paperR (l := l) T b mu

/-- The paper-faithful signed inequality is exactly M_paper >= 0. -/
theorem paperM_nonneg_iff_target :
    0 <= paperM (l := l) T b mu ↔ PaperTargetNormalization (l := l) T b mu := by
  unfold paperM paperA paperR PaperTargetNormalization
  constructor <;> intro h <;> linarith

/-- Conditional nonnegativity of M_paper from the paper-faithful comparison. -/
theorem paperM_nonneg_of_target
    (h : PaperTargetNormalization (l := l) T b mu) :
    0 <= paperM (l := l) T b mu :=
  (paperM_nonneg_iff_target (l := l) T b mu).mpr h

#check paperA
#check paperR
#check paperM
#check paperM_nonneg_iff_target
#check paperM_nonneg_of_target


end LeanFormal.IUT.XiFPaper.Mzk1PaperTargetNormalizationActual

end
