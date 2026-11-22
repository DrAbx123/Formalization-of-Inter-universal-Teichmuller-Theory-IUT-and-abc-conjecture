import LeanFormal.IUT.IUTII.Kummer.SourceLogShellAbsTopIIIBridge

/-!
# Mzk1AbsTopIIIBridgeTreeConsumerActual — consumer theorems over the tree AbsTopIII
invariant-image bridge (OLEAN_FRESH). Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1AbsTopIIIBridgeTreeConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum

universe u

/-- Consumer: bridge identification iff unit layer is contained in the pre-log-shell. -/
theorem consumer_iff_unitLayer_subset (D : SourceLogShellDatum.{u}) :
    SourceLogShellInvariantImageIdentification D ↔ D.unitLayer ⊆ D.preLogShell :=
  D.invariantImageIdentification_iff_unitLayer_subset

/-- Consumer: bridge identification iff every unit log-image lies in the pre-log-shell. -/
theorem consumer_iff_forall_log_mem (D : SourceLogShellDatum.{u}) :
    SourceLogShellInvariantImageIdentification D ↔
      ∀ u : D.Units, (D.logMap u).toAdd ∈ D.preLogShell :=
  D.invariantImageIdentification_iff_forall_log_mem

/-- Consumer: bridge identification implies the Kummer inclusion. -/
theorem consumer_codomainKummer (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) : D.codomainKummerContained :=
  D.codomainKummerContained_of_invariantImageIdentification h

/-- Consumer: the frozen calibration model satisfies the bridge identification. -/
theorem consumer_calibration :
    SourceLogShellInvariantImageIdentification sourceLogShellCalibrationDatum :=
  sourceLogShellCalibration_invariantImageIdentification

#check consumer_iff_unitLayer_subset
#check consumer_iff_forall_log_mem
#check consumer_codomainKummer
#check consumer_calibration

end LeanFormal.IUT.XiFPaper.Mzk1AbsTopIIIBridgeTreeConsumerActual
end
