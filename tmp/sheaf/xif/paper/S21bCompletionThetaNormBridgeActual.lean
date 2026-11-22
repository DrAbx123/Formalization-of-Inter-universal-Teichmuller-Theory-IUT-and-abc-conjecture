import tmp.sheaf.xif.paper.S21DegreeNormAlignmentActual
import tmp.sheaf.xif.paper.SignedLabelOneActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology

/-! # S21b: actual CompletionThetaNormBridge from a completion unit

Given an actual completion unit qUnit whose norm is the source theater theta
packet q, the unit itself witnesses CompletionThetaNormBridge at j = 1:

  ||qUnit|| = thetaPacket.q
            = thetaPacket.scale (oneLabel)
            = thetaValueAt n 0 (oneLabel).

Hence Real.log ||qUnit|| = Real.log (thetaValueAt ...).  This is an actual
completion unit, not a Prop-only bridge.

No fake equality/sorry/axiom/True/PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S21bCompletionThetaNormBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.S21DegreeNormAlignmentActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (n : ThetaPilotCarrier l)
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (K := I.initial.arithmetic.Fmod) p)

/-- The source theta value is the theater packet scale. -/
theorem thetaValueAt_eq_scale (j : SignedLabel l.value) :
    I.thetaValueAt (n.val : Int) 0 j =
      (I.theaterAt (n.val : Int) 0).thetaPacket.scale j := rfl

theorem thetaValueAt_representative_one_eq :
    I.thetaValueAt (n.val : Int) 0
        (SignedLabel.representative l (1 : ZMod l.value)) =
      I.thetaValueAt (n.val : Int) 0 (oneLabel l) := by
  congr 1
  apply SignedLabel.toFiniteLabel_injective l
  rw [SignedLabel.representative_toFl, SignedLabel.toFiniteLabel_apply,
    oneLabel_val]
  norm_num

/-- The j = 1 source theta value is the packet q. -/
theorem thetaValueAt_one_eq_q :
    I.thetaValueAt (n.val : Int) 0 (oneLabel l) =
      (I.theaterAt (n.val : Int) 0).thetaPacket.q := by
  rw [thetaValueAt_eq_scale (l := l) I n (oneLabel l),
    (I.theaterAt (n.val : Int) 0).thetaPacket.scale_eq]
  simp [oneLabel, realThetaValue, gaussExponent]

/-- An actual completion unit with the packet q norm witnesses
CompletionThetaNormBridge at j = 1. -/
theorem completionThetaNormBridge_of_completionUnit
    (qUnit : (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)ˣ)
    (hq : ‖(qUnit : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place)‖ =
      (I.theaterAt (n.val : Int) 0).thetaPacket.q) :
    CompletionThetaNormBridge (l := l) (I := I) n (place := place) := by
  refine ⟨(qUnit : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place), ?_, ?_⟩
  · exact norm_pos_iff.mpr (Units.ne_zero qUnit)
  · rw [hq, ← thetaValueAt_one_eq_q (l := l) I n,
      thetaValueAt_representative_one_eq (l := l) I n]

end LeanFormal.IUT.XiFPaper.S21bCompletionThetaNormBridgeActual

end
