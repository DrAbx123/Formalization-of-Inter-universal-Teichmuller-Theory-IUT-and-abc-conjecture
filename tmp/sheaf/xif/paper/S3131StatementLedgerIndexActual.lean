import LeanFormal.IUT.Audit.Status

/-! # S3131 statement-ledger index (data only) -/

namespace LeanFormal.IUT.XiFPaper.S3131StatementLedgerIndexActual

def S3131StatementLedgerIndex : List (String × String) :=
  [ ("S3131IUTIVTheoremAInputActual", "Theorem A shape + BD-class inequality (corpus 93-112)"),
    ("S3131IUTIVTheorem110InputActual", "Theorem 1.10 shape (log-volume estimates, p.1255/1363-1385)"),
    ("S3131IUTIVCor22Cor23InputActual", "Cor 2.2 (p.2380) / Cor 2.3 (p.3117) schemas + citation rows"),
    ("S3131IUTIVChainToABCActual", "logical chain shape + conditional theorem"),
    ("S3131GenEllInputDetailedActual", "GenEll Def 1.2/1.5, Ex 1.3, Props 1.4/1.7, Thm 2.1 (615-687)"),
    ("S3131GenEllEquivalenceShapeActual", "Thm 2.1 equivalence shape + reduction direction"),
    ("S3131Mzk1StatementActual", "[Mzk1] Noncritical Belyi statement schema"),
    ("S3131BDClassCompositionActual", "BD-class chain tools (class A)"),
    ("S3131IV110ConstantArithmeticActual", "Thm 1.10 constants d*_mod/e*_mod arithmetic (class A)"),
    ("S3131CitationStrengthAuditActual", "citation classification table 12 rows + 7 corrections"),
    ("S3131EndgameDependencyLedgerActual", "endgame node ledger + minimal conditional theorem"),
    ("S3136GenEllPaperStatementsActual / S3136GenEllStatementDetailsActual", "stage4 statement extractions (8/10 rows)") ]

theorem S3131StatementLedgerIndex_length : S3131StatementLedgerIndex.length = 12 := rfl

end LeanFormal.IUT.XiFPaper.S3131StatementLedgerIndexActual