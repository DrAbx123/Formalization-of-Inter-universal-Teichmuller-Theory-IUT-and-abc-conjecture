/-! # LeanFormal.IUT.XiFPaper.IUTExternalAbScStatementsActual — E2 [AbSc] Galois sections statements (class-D statement ledger)

STEP 0 prior-art: deep search for the [pGC]/[AbsAnb]/[AbSc]/[NodNon] objects: no
LeanFormal/ported definitions exist for pro-p Galois reconstruction, hyperbolic
absolute anabelian, Galois sections or nodal nondegeneracy; Mathlib has limits/
category theory/galois theory but no absolute anabelian layer.  Corpus [
AbSc] used
for the statement ledger.  Reuse: none at definition level yet.

LABEL: class-D external-object STATEMENT LAYER (proved:=false for every row).
No paper result is claimed or proved in this file. -/

namespace LeanFormal.IUT.XiFPaper.IUTExternalAbScStatementsActual

structure IUTExternalStatementRow where
  item : String
  corpus : String
  status : String
  proved : Bool

def iutExternalStatements : List IUTExternalStatementRow :=
  [ ⟨"Galois section definition/space", "[AbSc] §1", "STATEMENT (class D)", false⟩,
    ⟨"section reconstruction from local sections", "[AbSc] §2", "STATEMENT (class D)", false⟩,
    ⟨"Kummer/different compatibility of sections", "[AbSc] §3", "STATEMENT (class D)", false⟩,
    ⟨"non-abelian section conjecture shape", "[AbSc] §4", "STATEMENT (class D)", false⟩ ]

theorem iutExternalStatements_length : iutExternalStatements.length = 4 := rfl

#check iutExternalStatements
#check iutExternalStatements_length

end LeanFormal.IUT.XiFPaper.IUTExternalAbScStatementsActual