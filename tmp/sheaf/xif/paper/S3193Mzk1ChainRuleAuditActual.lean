import LeanFormal.IUT.Audit.Status

/-! # S3193: Mzk1 chain rule (stage4) + composition audit

No sorry/axiom. -/

namespace LeanFormal.IUT.Audit

/-- Chain rule rows. -/
def S3193Mzk1ChainRuleAudit : List (String × String × Nat × Nat × String) := [
  ("Mzk1PolyChainRuleActual.lean", "CITABLE", 5, 3264, "fresh EXIT=0"),
  ("Mzk1Lemma22CompositionActual.lean", "CITABLE", 9, 5574, "fresh EXIT=0 (updated)"),
  ("_S3193NewGreenProbe.lean", "EXIT=0 probe", 0, 0, "queued") ]

theorem S3193Mzk1ChainRuleAudit_length : S3193Mzk1ChainRuleAudit.length = 3 := rfl

/-- Content. -/
def S3193Mzk1ChainRuleContent : List String := [
  "polyMapPoints_comp_finite/infty PROVED (P1 composition on finite/infinity points)",
  "polyUnramifiedAt_comp_finite/infty PROVED (chain rule for unramifiedness; stage4 layer)",
  "comp_ne_zero_of_nonconstant PROVED",
  "Mzk1Lemma22Composition: comp/PreservesSet_comp/AvoidsPoint_comp/UnramifiedOver_comp + Mzk1Lemma22InductionStep + mzk1Lemma22_comp_witness PROVED (9 decls)",
  "=> stage4 chain rule layer PROVED; full 2.2 assembly to Thm2.5 unconditional next" ]

theorem S3193Mzk1ChainRuleContent_length : S3193Mzk1ChainRuleContent.length = 5 := rfl

/-- Record. -/
def S3193Mzk1ChainRuleAuditRecord : Obligation :=
  { id := "IUT.project.mzk1-chain-rule-audit"
    source := "post-resume audit 2026-11-10 12:50; checker+probe"
    status := VerificationStatus.interface
    note :=
      "MZK1 CHAIN RULE (stage4): Mzk1PolyChainRule CITABLE 5 decls 3264B — polyMapPoints_comp_"
      ++ "finite/infty + polyUnramifiedAt_comp_finite/infty + comp_ne_zero_of_nonconstant PROVED; "
      ++ "Mzk1Lemma22Composition updated CITABLE 9 decls 5574B (composition laws + comp_witness). "
      ++ "Stage4 chain rule layer PROVED; full 2.2 -> Thm2.5 unconditional assembly next."
    dependsOn := [ "S3192Mzk1StepConstructionAuditRecord" ] }

#check S3193Mzk1ChainRuleAuditRecord
#check S3193Mzk1ChainRuleAudit_length
#check S3193Mzk1ChainRuleContent_length

end LeanFormal.IUT.Audit
