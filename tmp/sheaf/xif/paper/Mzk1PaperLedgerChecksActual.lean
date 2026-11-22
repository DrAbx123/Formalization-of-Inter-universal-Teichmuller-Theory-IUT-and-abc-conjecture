import tmp.sheaf.xif.paper.Mzk1Cor312NumericalContentActual
import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract

/-! # Mzk1PaperLedgerChecksActual — paper-ledger numeric self-checks (chain-independent)

A545 self-check module (no new mathematics): records the paper-ledger numeric values of
the Cor 3.12 instance (Unit X: mu_q = -L/2, mu_theta = -L/6) as StepXI contract slots
and checks the Cor312Conclusion and the constant form independently of the pending
Kummer/FinalStatement chain.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperLedgerChecksActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Cor312NumericalContentActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual

/-- The numeric paper contract: q slot = mu_q(L), theta/target slot = mu_theta(L). -/
noncomputable def paperLedgerContract (L : Real) (hL : 0 < L)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) : StepXIContract :=
  signedCor312Contract (muQ L) (muTheta L)
    (by unfold muQ; linarith)
    ipl hipl she hshe apt hapt (cor312_numerical_holds L hL)

/-- Self-check: the numeric contract satisfies Corollary 3.12. -/
theorem paperLedger_cor312 (L : Real) (hL : 0 < L)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (paperLedgerContract L hL ipl hipl she hshe apt hapt) :=
  signedCor312_conclusion (muQ L) (muTheta L) (by unfold muQ; linarith)
    ipl hipl she hshe apt hapt (cor312_numerical_holds L hL)

/-- Self-check: q slot is negative. -/
theorem paperLedger_q_negative (L : Real) (hL : 0 < L) : muQ L < 0 := by
  unfold muQ
  linarith

/-- Self-check: the target slot equals the theta slot (identity by construction). -/
theorem paperLedger_target_identity (L : Real) (hL : 0 < L)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    (paperLedgerContract L hL ipl hipl she hshe apt hapt).targetSigned =
      muTheta L :=
  rfl

/-- Self-check: the genuine comparison is in `target_le_theta`, whose value is the
Unit X inequality mu_q <= mu_theta. -/
theorem paperLedger_comparison (L : Real) (hL : 0 < L)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    (paperLedgerContract L hL ipl hipl she hshe apt hapt).qSigned <=
      (paperLedgerContract L hL ipl hipl she hshe apt hapt).targetSigned :=
  (paperLedgerContract L hL ipl hipl she hshe apt hapt).q_le_target

#check paperLedgerContract
#check paperLedger_cor312
#check paperLedger_q_negative
#check paperLedger_target_identity
#check paperLedger_comparison

end LeanFormal.IUT.XiFPaper.Mzk1PaperLedgerChecksActual
end
