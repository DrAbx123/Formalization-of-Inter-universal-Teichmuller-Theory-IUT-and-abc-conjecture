import tmp.sheaf.xif.paper.S2959HalfIQHullCThetaUpperActual
import tmp.sheaf.xif.paper.S2752FinalHweightvolActual
import tmp.sheaf.xif.paper.ArithmeticLineBundleActual
import Mathlib.RingTheory.DedekindDomain.Different
import tmp.sheaf.xif.paper.S2771Gap1ClosedActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.XiFPaper.S2752FinalHweightvolActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.XiFPaper.S2715CThetaPaperScaleActual
open LeanFormal.IUT.XiFPaper.S2691ExactQNormalizationActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2990ActualDFpdActual

/-- The ring of integers of the Gaussian five-label arithmetic. -/
abbrev S2990R : Type := SourceOK (A := S2735Arithmetic S2771FiveLabel)

/-- Actual dFpd from the different ideal of the Gaussian field over Z. -/
noncomputable def S2990DFpd : Real :=
  (Ideal.absNorm (differentIdeal ℤ S2990R) : Real)

/-- Actual fFpd from the support ideal of an ABC triple. -/
noncomputable def S2990FFpd (a b c : Nat) : Real :=
  (Ideal.absNorm (S2752J S2771FiveLabel a b c) : Real)

/-- The actual different ideal is nonzero, so dFpd > 0. -/
theorem S2990DFpd_pos : 0 < S2990DFpd := by
  unfold S2990DFpd
  have hne : differentIdeal ℤ S2990R ≠ 0 := differentIdeal_ne_bot
  have hpos : 0 < Ideal.absNorm (differentIdeal ℤ S2990R) := by
    rw [Nat.pos_iff_ne_zero]
    intro h
    exact hne (Ideal.absNorm_eq_zero_iff.mp h)
  exact_mod_cast hpos

#check S2990DFpd
#check S2990FFpd
#check S2990DFpd_pos

end LeanFormal.IUT.XiFPaper.S2990ActualDFpdActual
end