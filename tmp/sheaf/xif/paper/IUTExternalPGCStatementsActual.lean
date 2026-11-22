/-! # LeanFormal.IUT.XiFPaper.IUTExternalPGCStatementsActual — E2 [pGC] local pro-p Galois reconstruction statements (class-D statement ledger)

STEP 0 prior-art: deep search for the [pGC]/[AbsAnb]/[AbSc]/[NodNon] objects: no
LeanFormal/ported definitions exist for pro-p Galois reconstruction, hyperbolic
absolute anabelian, Galois sections or nodal nondegeneracy; Mathlib has limits/
category theory/galois theory but no absolute anabelian layer.  Corpus [
pGC] used
for the statement ledger.  Reuse: none at definition level yet.

LABEL: class-D external-object STATEMENT LAYER (proved:=false for every row).
No paper result is claimed or proved in this file. -/

namespace LeanFormal.IUT.XiFPaper.IUTExternalPGCStatementsActual

structure IUTExternalStatementRow where
  item : String
  corpus : String
  status : String
  proved : Bool

def iutExternalStatements : List IUTExternalStatementRow :=
  [ ⟨"local pro-p group reconstruction", "[pGC] §1", "STATEMENT (class D)", false⟩,
    ⟨"pro-p absolute Galois group reconstruction from local data", "[pGC] §2", "STATEMENT (class D)", false⟩,
    ⟨"pro-p anabelian reconstruction of number fields", "[pGC] §3", "STATEMENT (class D)", false⟩,
    ⟨"local pro-p vs global comparison", "[pGC] §4", "STATEMENT (class D)", false⟩ ]

theorem iutExternalStatements_length : iutExternalStatements.length = 4 := rfl

#check iutExternalStatements
#check iutExternalStatements_length

end LeanFormal.IUT.XiFPaper.IUTExternalPGCStatementsActual