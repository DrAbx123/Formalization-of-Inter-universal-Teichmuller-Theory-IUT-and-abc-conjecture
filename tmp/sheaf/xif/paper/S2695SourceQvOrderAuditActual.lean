import tmp.sheaf.xif.paper.SourceQvCandidateActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.SourceQvClosed
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.SourceQvCandidateActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2695SourceQvOrderAuditActual

universe u
variable {F : Type u} [Field F] [NumberField F]
variable (v : NumberField.FinitePlace F)
variable (X : PuncturedEllipticCurve F)
variable (hsplit : X.HasSplitMultiplicativeReductionAt v)

/-- Actual norm/order relation for the source q_v candidate: if the residue
norm is 5, its norm is 5^(-exponent), hence exact norm 1/5 iff order 1. -/
theorem S2695SourceQvCandidate_norm_eq_zpow
    (h5 : residueNormBase v = 5) :
    ‖(sourceQvCandidate v X hsplit).q‖ =
      (5 : Real) ^ (-(sourceQvCandidate v X hsplit).exponent) := by
  rw [qNorm_eq_residueNormBase_zpow, h5]

theorem S2695SourceQvCandidate_order_pos :
    0 < (sourceQvCandidate v X hsplit).order :=
  (sourceQvCandidate v X hsplit).order_pos

theorem S2695SourceQvCandidate_norm_inv_five_iff_order_one
    (h5 : residueNormBase v = 5) :
    ‖(sourceQvCandidate v X hsplit).q‖ = ((5 : Real)⁻¹) ↔
      (sourceQvCandidate v X hsplit).order = 1 := by
  rw [S2695SourceQvCandidate_norm_eq_zpow v X hsplit h5]
  have hinj : Function.Injective (fun n : Int => (5 : Real) ^ n) :=
    zpow_right_injective₀ (by norm_num : (0 : Real) < 5) (by norm_num)
  constructor
  · intro h
    have hpow : (5 : Real) ^ (-(sourceQvCandidate v X hsplit).exponent) =
        (5 : Real) ^ (-1 : Int) := by simpa using h
    have he : -(sourceQvCandidate v X hsplit).exponent = -1 := hinj hpow
    have hexp : (sourceQvCandidate v X hsplit).exponent = 1 := by omega
    rw [FinitePlaceQCandidate.order, hexp]
    norm_num
  · intro h
    have hexp : (sourceQvCandidate v X hsplit).exponent = 1 := by
      have hcast := qOrder_cast_eq_exponent_cast (sourceQvCandidate v X hsplit)
      rw [h] at hcast
      norm_num at hcast
      exact_mod_cast hcast.symm
    rw [hexp]
    norm_num

/-- The source q_v structure supplies only order > 0; it does not determine
whether the order is 1 or larger. -/
def S2695SourceQvCandidateExactOrderOne : Prop :=
  (sourceQvCandidate v X hsplit).order = 1

theorem S2695SourceQvCandidate_order_cases :
    (sourceQvCandidate v X hsplit).order = 1 ∨
      1 < (sourceQvCandidate v X hsplit).order := by
  have hp := S2695SourceQvCandidate_order_pos v X hsplit
  omega

#print axioms S2695SourceQvCandidate_norm_inv_five_iff_order_one
#print axioms S2695SourceQvCandidate_order_cases

end LeanFormal.IUT.XiFPaper.S2695SourceQvOrderAuditActual
end
