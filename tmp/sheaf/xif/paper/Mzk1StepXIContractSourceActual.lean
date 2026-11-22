import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1StepXIContractSourceActual — IUT III Step (xi): contract from explicit source data

DAG node: iutiv-abc:StepXI (StepXIContract / Cor312Conclusion).
Contract.lean leaves the *construction* of StepXIContract from IUT source data
unfinished.  This file gives the source-facing construction pattern: an explicit
StepXISourceData record (q/theta/target signed reals, q<0, q<=target<=theta, and
the IPL/SHE/APT propositions with their evidence) yields a StepXIContract, and hence
Cor312Conclusion.  The source data itself remains named; no placeholder contract is
asserted to exist.

No closure claim; GATE NOT PASSED; registry 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXIContractSourceActual

open LeanFormal.IUT

/-- Explicit source-side data for the IUT III Step (xi) contract. -/
structure StepXISourceData where
  qSigned : Real
  thetaSigned : Real
  targetSigned : Real
  q_negative : qSigned < 0
  q_le_target : qSigned ≤ targetSigned
  target_le_theta : targetSigned ≤ thetaSigned
  ipl : Prop
  she : Prop
  apt : Prop
  ipl_evidence : ipl
  she_evidence : she
  apt_evidence : apt

/-- Construct the StepXI contract from explicit source data. -/
def stepXIContract_of_sourceData (D : StepXISourceData) : StepXIContract :=
{ qSigned := D.qSigned
  thetaSigned := D.thetaSigned
  targetSigned := D.targetSigned
  q_negative := D.q_negative
  ipl := D.ipl
  she := D.she
  apt := D.apt
  ipl_evidence := D.ipl_evidence
  she_evidence := D.she_evidence
  apt_evidence := D.apt_evidence
  q_le_target := D.q_le_target
  target_le_theta := D.target_le_theta }

/-- The ordered Cor 3.12 conclusion from explicit source data. -/
theorem cor312Conclusion_of_sourceData (D : StepXISourceData) :
    Cor312Conclusion (stepXIContract_of_sourceData D) :=
  cor312_of_constructed_stepXI (stepXIContract_of_sourceData D)

/-- The contract's q is negative. -/
theorem q_negative_of_sourceData (D : StepXISourceData) :
    (stepXIContract_of_sourceData D).qSigned < 0 :=
  (stepXIContract_of_sourceData D).q_negative

/-- Rows: source-data bridge status. -/
def stepXISourceRows : List (String × String × String) :=
  [ ("contract construction", "stepXIContract_of_sourceData", "DEF (explicit source data)"),
    ("Cor 3.12 conclusion", "cor312Conclusion_of_sourceData", "PROVED (conditional on source data)"),
    ("q negativity", "q_negative_of_sourceData", "PROVED (conditional)"),
    ("source data", "q/theta/target + IPL/SHE/APT evidence", "NAMED (not constructed here)"),
    ("scope", "no closure; gate NOT PASSED", "INTEGRITY") ]

theorem stepXISourceRows_length : stepXISourceRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1StepXIContractSourceActual

end
