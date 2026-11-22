/-! # LeanFormal.IUT.XiFPaper.IUTExternalNodNonStatementsActual — E2 [NodNon] nodal nondegeneracy statements (class-D statement ledger)

STEP 0 prior-art: deep search for the [pGC]/[AbsAnb]/[AbSc]/[NodNon] objects: no
LeanFormal/ported definitions exist for pro-p Galois reconstruction, hyperbolic
absolute anabelian, Galois sections or nodal nondegeneracy; Mathlib has limits/
category theory/galois theory but no absolute anabelian layer.  Corpus [
NodNon] used
for the statement ledger.  Reuse: none at definition level yet.

LABEL: class-D external-object STATEMENT LAYER (proved:=false for every row).
No paper result is claimed or proved in this file. -/

namespace LeanFormal.IUT.XiFPaper.IUTExternalNodNonStatementsActual

structure IUTExternalStatementRow where
  item : String
  corpus : String
  status : String
  proved : Bool

def iutExternalStatements : List IUTExternalStatementRow :=
  [ ⟨"nodal curve / stable reduction definitions", "[NodNon] §1", "STATEMENT (class D)", false⟩,
    ⟨"nodal nondegeneracy of the tempered fundamental group", "[NodNon] §2", "STATEMENT (class D)", false⟩,
    ⟨"nondegeneracy under degenerating families", "[NodNon] §3", "STATEMENT (class D)", false⟩,
    ⟨"reconstruction of the dual graph", "[NodNon] §4", "STATEMENT (class D)", false⟩ ]

theorem iutExternalStatements_length : iutExternalStatements.length = 4 := rfl

#check iutExternalStatements
#check iutExternalStatements_length

end LeanFormal.IUT.XiFPaper.IUTExternalNodNonStatementsActual