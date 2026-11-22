import LeanFormal.IUT.IUTIII.Corollary312.StepXI.FiniteCertificateBridge
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1StepXICertificateActual — StepXI contract from an explicit finite certificate

DAG node: iutiv-abc:StepXI.  A StepXIFiniteCertificate together with its
FiniteStepXILinkEvidence yields a concrete StepXIContract and its ordered
Cor312Conclusion.  This is the finite-certificate route into the StepXI contract;
the certificate data (including its source-side evidence) remains explicit.

No closure claim; GATE NOT PASSED; registry 14041; no registry edits.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1StepXICertificateActual

open LeanFormal.IUT

universe u

/-- The contract extracted from a finite certificate and its link evidence. -/
def stepXIContract_of_finiteCertificate {label : Type u} [Fintype label]
    (C : StepXIFiniteCertificate label) (E : FiniteStepXILinkEvidence C) :
    StepXIContract :=
  C.toContract E

/-- The finite-certificate contract satisfies the ordered Cor 3.12 conclusion. -/
theorem cor312Conclusion_of_finiteCertificate {label : Type u} [Fintype label]
    (C : StepXIFiniteCertificate label) (E : FiniteStepXILinkEvidence C) :
    Cor312Conclusion (stepXIContract_of_finiteCertificate C E) :=
  cor312_of_finite_certificate C E

/-- The certificate contract has negative q. -/
theorem q_negative_of_finiteCertificate {label : Type u} [Fintype label]
    (C : StepXIFiniteCertificate label) (E : FiniteStepXILinkEvidence C) :
    (stepXIContract_of_finiteCertificate C E).qSigned < 0 :=
  (stepXIContract_of_finiteCertificate C E).q_negative

/-- Existence of a concrete StepXI contract from a finite certificate. -/
theorem exists_stepXIContract_of_finiteCertificate {label : Type u} [Fintype label]
    (C : StepXIFiniteCertificate label) (E : FiniteStepXILinkEvidence C) :
    ∃ contract : StepXIContract, contract.qSigned < 0 ∧ Cor312Conclusion contract :=
  ⟨stepXIContract_of_finiteCertificate C E,
    q_negative_of_finiteCertificate C E,
    cor312Conclusion_of_finiteCertificate C E⟩

/-- Rows: finite-certificate StepXI status. -/
def stepXICertificateRows : List (String × String × String) :=
  [ ("contract extraction", "stepXIContract_of_finiteCertificate", "DEF (certificate route)"),
    ("Cor312 conclusion", "cor312Conclusion_of_finiteCertificate", "PROVED (conditional on certificate+evidence)"),
    ("q negativity", "q_negative_of_finiteCertificate", "PROVED"),
    ("existence", "exists_stepXIContract_of_finiteCertificate", "PROVED (conditional)"),
    ("scope", "certificate/link evidence explicit; no closure; gate NOT PASSED", "INTEGRITY") ]

theorem stepXICertificateRows_length : stepXICertificateRows.length = 5 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1StepXICertificateActual

end
