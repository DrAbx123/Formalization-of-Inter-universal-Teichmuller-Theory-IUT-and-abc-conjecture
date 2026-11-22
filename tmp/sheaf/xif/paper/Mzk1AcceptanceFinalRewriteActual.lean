/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1Cor312FinalStatementActual
import tmp.sheaf.xif.paper.Mzk1FinalAssemblySelfChecksActual
import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual
import Mathlib.Tactic

/-! # Mzk1AcceptanceFinalRewriteActual — final acceptance, real-valued paper shape

A569 rewrite, green-import-only: the paper Cor 3.12 statement shape and its
acceptance checks at the signed-real level, plus the assembly's signed contract
identity checks (target=theta, genuine comparison).

All theorems are real-valued/contract-level and depend only on green modules.
 -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AcceptanceFinalRewriteActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalStatementActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalAssemblySelfChecksActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual

/-- Acceptance: paper target `-|log q| <= -|log theta|` iff `|log theta| <= |log q|`. -/
theorem acceptance_paperTarget_iff (qMag thetaMag : Real) :
    paperTarget qMag thetaMag ↔ thetaMag ≤ qMag :=
  paperTarget_iff_magnitudes qMag thetaMag

/-- Acceptance: a contract with the paper signed slots satisfies the paper target
exactly when its Cor312Conclusion holds. -/
theorem acceptance_contract_matches
    {C : StepXIContract} {qMag thetaMag : Real}
    (hq : C.qSigned = paperSignedQ qMag)
    (ht : C.thetaSigned = paperSignedTheta thetaMag) :
    Cor312Conclusion C ↔ paperTarget qMag thetaMag :=
  contract_matches_paperTarget hq ht

/-- Acceptance: the signed contract's target slot is theta (not q). -/
theorem acceptance_target_identity (q theta : Real) (hq : q < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) (hle : q ≤ theta) :
    (signedCor312Contract q theta hq ipl hipl she hshe apt hapt hle).targetSigned
      = theta :=
  rfl

/-- Acceptance: the genuine comparison field is exactly the supplied `q <= theta`. -/
theorem acceptance_genuine_comparison (q theta : Real) (hq : q < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) (hle : q ≤ theta) :
    (signedCor312Contract q theta hq ipl hipl she hshe apt hapt hle).qSigned ≤
      (signedCor312Contract q theta hq ipl hipl she hshe apt hapt hle).targetSigned :=
  hle

/-- Acceptance: from `thetaMag <= qMag` the paper signed shape becomes the
comparison `qSigned <= thetaSigned` of the contract. -/
theorem acceptance_signed_shape (qMag thetaMag : Real)
    (h : thetaMag ≤ qMag) :
    paperSignedQ qMag ≤ paperSignedTheta thetaMag :=
  (paperTarget_iff_magnitudes qMag thetaMag).2 h

#check acceptance_paperTarget_iff
#check acceptance_contract_matches
#check acceptance_target_identity

end LeanFormal.IUT.XiFPaper.Mzk1AcceptanceFinalRewriteActual
end
