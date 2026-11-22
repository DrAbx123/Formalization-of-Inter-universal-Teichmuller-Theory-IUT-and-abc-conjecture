/-
  Owned metadata probe (final) for the Step XI whole-boundary audit.
  Contract: stepxi-whole-boundary-audit-v1
  Run: core-stepxi-boundary-20261014
  Owner: dsh_stepxi_boundary_owner, generation 2

  Scope: public imports, #check of public types/signatures, #print axioms, and
  existence probes only. No implementation bodies are printed.
  Note: `import LeanFormal.IUT.ABCBridge.Bridge` was tested separately and fails
  because its object file does not exist; the module is therefore not imported here.
-/

import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.IPL
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SHE
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.APT

namespace CoreStepXIBoundaryAudit

-- Public signature surface actually exported by the Step XI boundary files.
#check LeanFormal.IUT.StepXIContract
#check LeanFormal.IUT.Cor312Conclusion
#check @LeanFormal.IUT.cor312_of_constructed_stepXI
#check @LeanFormal.IUT.q_positive_of_constructed_stepXI
#check LeanFormal.IUT.WallObligation
#check LeanFormal.IUT.Audit.stepXIContractConstruction

-- Types needed to interpret the audit obligation record.
#check LeanFormal.IUT.Audit.Obligation
#check LeanFormal.IUT.Audit.VerificationStatus
#check LeanFormal.IUT.Audit.VerificationStatus.pending

-- Axiom footprint of the exported Step XI theorems.
#print axioms LeanFormal.IUT.cor312_of_constructed_stepXI
#print axioms LeanFormal.IUT.q_positive_of_constructed_stepXI

-- Existence probe for the named source-construction theorem. Succeeds iff absent.
#check_failure LeanFormal.IUT.theorem311_produces_stepXI_contract

end CoreStepXIBoundaryAudit
