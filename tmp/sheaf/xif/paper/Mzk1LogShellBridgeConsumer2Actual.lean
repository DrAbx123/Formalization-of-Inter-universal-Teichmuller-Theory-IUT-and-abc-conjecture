import tmp.sheaf.xif.paper.Mzk1Prop58iImagesActual
import tmp.sheaf.xif.paper.Mzk1Prop58iTargetActual
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellAbsTopIIIBridge

/-!
# Mzk1LogShellBridgeConsumer2Actual — consumer theorems combining the tree AbsTopIII
bridge with our concrete target/images layer (all EXIT0 / OLEAN_FRESH).
Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LogShellBridgeConsumer2Actual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iImagesActual
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iTargetActual

universe u

/-- Consumer: the frozen calibration model satisfies the bridge identification (tree). -/
theorem consumer_calibration_bridge :
    SourceLogShellInvariantImageIdentification sourceLogShellCalibrationDatum :=
  sourceLogShellCalibration_invariantImageIdentification

/-- Consumer: the frozen calibration model satisfies the reconstruction target. -/
theorem consumer_calibration_target :
    prop58iReconstructionTarget sourceLogShellCalibrationDatum :=
  calibration_reconstructionTarget

/-- Consumer: the target is equivalent to the bridge card (both directions). -/
theorem consumer_target_iff_bridge (D : SourceLogShellDatum.{u}) :
    prop58iReconstructionTarget D ↔ SourceLogShellInvariantImageIdentification D :=
  prop58iReconstructionTarget_iff_bridge D

/-- Consumer: under the bridge, logShell equals the inv-scaled unit layer (tree). -/
theorem consumer_bridge_logShell (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) :
    D.logShell = D.invScaledUnitLayer :=
  D.logShell_eq_invScaledUnitLayer_of_invariantImageIdentification h

/-- Consumer: the invariant submonoid image is the pre-log-shell (P58IMG). -/
theorem consumer_preLogShell_image (D : SourceLogShellDatum.{u}) :
    D.preLogShell = (fun u : D.Units => (D.logMap u).toAdd) '' (D.invariants : Set D.Units) :=
  preLogShell_eq_image_invariants D

#check consumer_calibration_bridge
#check consumer_calibration_target
#check consumer_target_iff_bridge
#check consumer_bridge_logShell
#check consumer_preLogShell_image

end LeanFormal.IUT.XiFPaper.Mzk1LogShellBridgeConsumer2Actual
end
