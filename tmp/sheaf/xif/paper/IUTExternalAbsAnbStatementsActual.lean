/-! # LeanFormal.IUT.XiFPaper.IUTExternalAbsAnbStatementsActual — E2 [AbsAnb] hyperbolic absolute anabelian statements (class-D statement ledger)

STEP 0 prior-art: deep search for the [pGC]/[AbsAnb]/[AbSc]/[NodNon] objects: no
LeanFormal/ported definitions exist for pro-p Galois reconstruction, hyperbolic
absolute anabelian, Galois sections or nodal nondegeneracy; Mathlib has limits/
category theory/galois theory but no absolute anabelian layer.  Corpus [
AbsAnb] used
for the statement ledger.  Reuse: none at definition level yet.

LABEL: class-D external-object STATEMENT LAYER (proved:=false for every row).
No paper result is claimed or proved in this file. -/

namespace LeanFormal.IUT.XiFPaper.IUTExternalAbsAnbStatementsActual

structure IUTExternalStatementRow where
  item : String
  corpus : String
  status : String
  proved : Bool

def iutExternalStatements : List IUTExternalStatementRow :=
  [ ⟨"hyperbolic curve reconstruction from fundamental group", "[AbsAnb] §1", "STATEMENT (class D)", false⟩,
    ⟨"stabilizer/center reconstruction", "[AbsAnb] §2", "STATEMENT (class D)", false⟩,
    ⟨"tempered/geometric fundamental group reconstruction", "[AbsAnb] §3", "STATEMENT (class D)", false⟩,
    ⟨"outer representation reconstruction", "[AbsAnb] §4", "STATEMENT (class D)", false⟩ ]

theorem iutExternalStatements_length : iutExternalStatements.length = 4 := rfl

#check iutExternalStatements
#check iutExternalStatements_length

end LeanFormal.IUT.XiFPaper.IUTExternalAbsAnbStatementsActual