import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import LeanFormal.IUT.IUTIII.Corollary312.Comparison
import LeanFormal.IUT.Audit.Status

/-!
# ShehddIUT312TopStatementActual — formal statement layer for IUT III Cor 3.12

Paper IUT III Cor 3.12 (Log-volume Estimates for Theta-Pilot Objects):
  -|log(Theta)| >= -|log(q)|   (i.e. CTheta >= -1)
for the procession-normalized mono-analytic log-volume of the holomorphic hull of the
possible images of a Theta-pilot object (multiradial representation, relative to the
Kummer isomorphisms, subject to Ind1/Ind2/Ind3), compared with the log-volume of a
q-pilot object.

The Lean `StepXIContract` (IUTIII/Corollary312/StepXI/Contract.lean) carries the signed
normalizations qSigned/thetaSigned/targetSigned together with the ordered chain
qSigned <= targetSigned <= thetaSigned and qSigned < 0.  This file records the exact
statement-level mapping between the paper inequality and the Lean contract, and proves
the contract => statement direction (no new assumptions, no sorry/axiom).
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddIUT312TopStatementActual

open LeanFormal.IUT

/-- Statement-level form of IUT III Cor 3.12 in the Lean contract: the signed
normalizations satisfy qSigned <= thetaSigned (the `-|log Theta| >= -|log q|`
estimate after sign normalisation). -/
def IUT312TopStatement (contract : StepXIContract) : Prop :=
  contract.qSigned ≤ contract.thetaSigned

/-- The statement-level form is exactly the tree `Cor312Conclusion`. -/
theorem iut312TopStatement_iff_cor312Conclusion (contract : StepXIContract) :
    IUT312TopStatement contract ↔ Cor312Conclusion contract := Iff.rfl

/-- **PROVED (conditional on a contract):** the paper's Cor 3.12 inequality holds for
any StepXI contract (ordered chain qSigned <= targetSigned <= thetaSigned). -/
theorem iut312TopStatement_of_contract (contract : StepXIContract) :
    IUT312TopStatement contract := cor312_of_constructed_stepXI contract

/-- The statement-level inequality as a pure order chain. -/
theorem iut312TopStatement_chain {q target theta : ℝ} (h1 : q ≤ target)
    (h2 : target ≤ theta) : q ≤ theta := le_trans h1 h2

/-- Row record: paper statements vs Lean statement layer. -/
def iut312TopStatementRows : List (String × String × String) :=
  [ ("paper Cor 3.12 inequality -|log Theta| >= -|log q|", "STATEMENT", "IUT312TopStatement contract := contract.qSigned <= contract.thetaSigned")
  , ("CTheta >= -1 shape", "STATEMENT", "signed normalisation qSigned <= thetaSigned; qSigned < 0 carried by StepXIContract")
  , ("contract => statement", "PROVED", "iut312TopStatement_of_contract (uses tree cor312_of_constructed_stepXI)")
  , ("statement <=> tree Cor312Conclusion", "PROVED", "iut312TopStatement_iff_cor312Conclusion (Iff.rfl)")
  , ("Theta-pilot/q-pilot/hull/Kummer/multiradial/Ind objects themselves", "NAMED elsewhere", "iut-skeleton and e-deep/EtTh/AbsTopIII nodes; see coord/SURVEY-shehdd.md") ]

theorem iut312TopStatementRows_length : iut312TopStatementRows.length = 5 := rfl

#check IUT312TopStatement
#check iut312TopStatement_iff_cor312Conclusion
#check iut312TopStatement_of_contract
#check iut312TopStatement_chain
#check iut312TopStatementRows_length

end LeanFormal.IUT.XiFPaper.ShehddIUT312TopStatementActual
end
