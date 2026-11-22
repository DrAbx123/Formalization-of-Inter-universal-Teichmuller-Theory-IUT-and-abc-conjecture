/-! # IUTExternalCbGCStatementsActual — E1 [CbGC] combinatorial reconstruction statements

STEP 0 prior-art: deep search 'CbGC|combinatorial reconstruction|configuration space|
anabelioid' -> no LeanFormal/ported definition; Mathlib has category theory only.
Corpus papers: [CbGC] and [Config] statement ledger; IUTExternalConfigDefsActual has
the configuration-space definitions (PROVED definition layer).

LABEL: class-D external-object statement ledger (proved:=false for every row).
No paper result is claimed. -/

namespace LeanFormal.IUT.XiFPaper.IUTExternalCbGCStatementsActual

structure IUTExternalCbGCStatementRow where
  item : String
  corpus : String
  status : String
  proved : Bool

def iutExternalCbGCStatements : List IUTExternalCbGCStatementRow :=
  [ ⟨"combinatorial reconstruction of anabelioids from configuration spaces", "[CbGC] §1", "STATEMENT (class D)", false⟩,
    ⟨"reconstruction of the tempered fundamental group", "[CbGC] §2", "STATEMENT (class D)", false⟩,
    ⟨"configuration-space comparison morphisms", "[CbGC] §3", "STATEMENT (class D)", false⟩,
    ⟨"absolute anabelian reconstruction via configuration spaces", "[CbGC] §4", "STATEMENT (class D)", false⟩ ]

theorem iutExternalCbGCStatements_length : iutExternalCbGCStatements.length = 4 := rfl

#check iutExternalCbGCStatements_length

end LeanFormal.IUT.XiFPaper.IUTExternalCbGCStatementsActual