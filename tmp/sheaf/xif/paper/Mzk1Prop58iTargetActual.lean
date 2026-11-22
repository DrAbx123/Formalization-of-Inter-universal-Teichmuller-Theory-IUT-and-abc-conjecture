import tmp.sheaf.xif.paper.Mzk1Prop58iConcreteActual
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellAbsTopIIIBridge

/-!
# Mzk1Prop58iTargetActual — the Prop 5.8(i) reconstruction target at the model level

STEP 0 prior-art: SourceLogShellCarrier (unitLayer/preLogShell/logShell),
SourceLogShellAbsTopIIIBridge (SourceLogShellInvariantImageIdentification, calibration
theorem, codomainKummerContained/logShell_eq_invScaled consequences),
Mzk1Prop58iConcreteActual (concrete invariants) -> REUSE.

WHAT THIS FILE DOES:
* states the model form of the Prop 5.8(i) reconstruction target
  (O^◇/unit image = invariant image), proves its equivalence with the bridge card,
  proves it on the frozen calibration model, and derives the Kummer inclusion and the
  concrete log-shell identification from it;
* records the rows and keeps the group-theoretic algorithm itself NAMED.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Prop58iTargetActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iConcreteActual

universe u

/-- The model-level Prop 5.8(i) reconstruction target: the unit image equals the invariant
image (the concrete O^◇-image is the Galois-invariant unit image). -/
def prop58iReconstructionTarget (D : SourceLogShellDatum.{u}) : Prop :=
  D.unitLayer = D.preLogShell

/-- The target is equivalent to the bridge card (the two sides are swapped by eq_comm). -/
theorem prop58iReconstructionTarget_iff_bridge (D : SourceLogShellDatum.{u}) :
    prop58iReconstructionTarget D ↔ SourceLogShellInvariantImageIdentification D :=
  Iff.rfl

/-- The frozen calibration model satisfies the reconstruction target (tree calibration
theorem). -/
theorem calibration_reconstructionTarget :
    prop58iReconstructionTarget sourceLogShellCalibrationDatum :=
  sourceLogShellCalibration_invariantImageIdentification

/-- The target implies the Kummer inclusion unitLayer ⊆ logShell (bridge consequence). -/
theorem target_implies_kummerInclusion (D : SourceLogShellDatum.{u})
    (h : prop58iReconstructionTarget D) : D.unitLayer ⊆ D.logShell :=
  D.codomainKummerContained_of_invariantImageIdentification
    ((prop58iReconstructionTarget_iff_bridge D).mp h)

/-- The target implies the concrete log-shell identification
logShell = (p*_v)^{-1}·unitLayer (bridge consequence). -/
theorem target_implies_logShell_eq (D : SourceLogShellDatum.{u})
    (h : prop58iReconstructionTarget D) : D.logShell = D.invScaledUnitLayer :=
  D.logShell_eq_invScaledUnitLayer_of_invariantImageIdentification
    ((prop58iReconstructionTarget_iff_bridge D).mp h)

/-- Target rows: (item, statement, status). -/
def prop58iTargetRows : List (String × String × String) :=
  [ ("reconstruction target (model form)", "unitLayer = preLogShell", "DEFINED"),
    ("target <=> bridge card", "prop58iReconstructionTarget_iff_bridge", "PROVED (eq_comm)"),
    ("calibration model satisfies target", "calibration_reconstructionTarget", "PROVED (tree calibration)"),
    ("target => Kummer inclusion", "target_implies_kummerInclusion", "PROVED (bridge consequence)"),
    ("target => log-shell = (p*)^-1 unitLayer", "target_implies_logShell_eq", "PROVED (bridge consequence)"),
    ("group-theoretic reconstruction algorithm", "not asserted", "NAMED (paper deep input)") ]

/-- The target row record has six rows. -/
theorem prop58iTargetRows_length : prop58iTargetRows.length = 6 := rfl

#check prop58iReconstructionTarget
#check prop58iReconstructionTarget_iff_bridge
#check calibration_reconstructionTarget
#check target_implies_kummerInclusion
#check target_implies_logShell_eq
#check prop58iTargetRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Prop58iTargetActual
end
