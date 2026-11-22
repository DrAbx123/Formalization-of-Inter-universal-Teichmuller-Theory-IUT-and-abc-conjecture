import tmp.sheaf.xif.paper.S3131Mzk1StatementActual

/-! # Mzk1Section1StatementsActual — [Mzk1] §1 exact statements + classification

PAPER: Mochizuki, Noncritical Belyi Maps (corpus:
papers/motizuki_corpus/text/Noncritical Belyi Maps.txt), §1 lines 1-42.

PRIOR ART (STEP 0, not re-proved): tmp/sheaf/xif/paper/S3131Mzk1StatementActual
(NoncriticalBelyiStatement + 2 citation rows; imported below).

LABEL: exact paper-input statement ledger (data) + provability classification.
No Belyi-map theorem is claimed as proved. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Section1StatementsActual

open LeanFormal.IUT.XiFPaper.S3131Mzk1StatementActual

/-- Reuse: the prior-art Mzk1 statement wrapper is the identity on the input proposition. -/
theorem mzk1_def11_reuse (P : Prop) : NoncriticalBelyiStatement P ↔ P := Iff.rfl

structure Mzk1StatementRow where
  label : String
  lineRange : String
  content : String
  classification : String

def mzk1Section1Statements : List Mzk1StatementRow :=
  [ ⟨"Definition 1.1", "16-26", "a dominant morphism of Q-schemes phi : X -> P^1_Q is a Belyi map if phi is unramified over the open subscheme U_P = P^1_Q minus {0,1,infinity}; U_X = phi^{-1}(U_P) is a Belyi open of X. Every X admits at least one Belyi open ([1]).", "DEFINITION (scheme-theoretic; stateable as a data structure with unramifiedness over the complement; no full proof needed)"⟩,
    ⟨"Corollary 1.2", "31-34", "Belyi Opens as a Zariski Base: if V_X <= X is an open subscheme containing a closed point x, then there exists a Belyi open U_X with U_X <= V_X and x in U_X; in particular Belyi opens form a base for the Zariski topology of X.", "DEEP CONSEQUENCE of Theorem 2.5 (paper-input); not a definition"⟩ ]

theorem mzk1Section1Statements_length : mzk1Section1Statements.length = 2 := rfl

#check mzk1_def11_reuse
#check mzk1Section1Statements_length

end LeanFormal.IUT.XiFPaper.Mzk1Section1StatementsActual