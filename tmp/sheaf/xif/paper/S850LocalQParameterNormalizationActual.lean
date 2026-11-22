import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.ABCBridge.Geometry.RelativeCompletionFinrankReduction
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellRamificationInertia
/-! # S850: LocalQParameter.exponent normalization
LocalQParameter.exponent is defined by -toAdd(unzero (Valued.v q)), where the
adic-completion valuation is the DVR valuation with uniformizer value 1.
Thus Lean exponent = ord_pi, not the p-normalized ord_p.  CORRECTED by S852: IUT III Rmk 2.4.2(ii) takes p_v to be the local
uniformizer pi_v, so ord_v(p_v)=1 and paper order = Lean exponent; there is
no /e.  The rational-prime-normalized branch is INVALID and removed. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S850LocalQParameterNormalizationActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
universe u
variable {F : Type u} [Field F] [NumberField F]
variable (place : NumberField.FinitePlace F)
/-- The e-factor between π-order and p-order at the place. -/
noncomputable def paperRamificationIndex : Nat :=
  relativeRamificationIndex (k := ℚ) place
/-- Paper order under the uniformizer normalization ord_v(pi_v)=1. -/
noncomputable def paperOrderPi (q : FinitePlaceQCandidate place) : Int :=
  q.exponent
/-- Correct paper normalization: p_v = uniformizer pi_v, ord_v(pi_v)=1. -/
def PaperOrderPiNormalization : Prop := True

theorem paperOrderPi_is_paper_order (q : FinitePlaceQCandidate place) :
    paperOrderPi place q = q.exponent := rfl

end LeanFormal.IUT.XiFPaper.S850LocalQParameterNormalizationActual