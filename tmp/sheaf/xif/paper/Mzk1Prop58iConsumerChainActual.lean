import tmp.sheaf.xif.paper.Mzk1Prop58iConcreteActual
import tmp.sheaf.xif.paper.Mzk1Prop58iTargetActual
import tmp.sheaf.xif.paper.Mzk1Prop58iImagesActual
import tmp.sheaf.xif.paper.Mzk1P58iInvariantsAlgorithmActual

/-!
# Mzk1Prop58iConsumerChainActual — consumer theorems for Prop 5.8(i) concrete/refined
assets (P58I/P58IT/P58IMG/P58ALG, all EXIT0). Composed projections only; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Prop58iConsumerChainActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iConcreteActual
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iTargetActual
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iImagesActual
open LeanFormal.IUT.XiFPaper.Mzk1P58iInvariantsAlgorithmActual

universe u

/-- Consumer: target implies the Kummer inclusion (from P58IT). -/
theorem consumer_target_kummerInclusion (D : SourceLogShellDatum.{u})
    (h : prop58iReconstructionTarget D) : D.unitLayer ⊆ D.logShell :=
  target_implies_kummerInclusion D h

/-- Consumer: target implies logShell = inv-scaled unit layer (from P58IT). -/
theorem consumer_target_logShell_eq (D : SourceLogShellDatum.{u})
    (h : prop58iReconstructionTarget D) : D.logShell = D.invScaledUnitLayer :=
  target_implies_logShell_eq D h

/-- Consumer: the invariant image is exactly the log-image of invariants (P58IMG). -/
theorem consumer_preLogShell_image (D : SourceLogShellDatum.{u}) :
    D.preLogShell = (fun u : D.Units => (D.logMap u).toAdd) '' (D.invariants : Set D.Units) :=
  preLogShell_eq_image_invariants D

/-- Consumer: extracted p* equals the paper/tree p*. -/
theorem consumer_pStar (I : LocalFieldInvariantsData) : I.pStar = sourceLogShellStar I.p :=
  LocalFieldInvariantsData.pStar_eq_sourceLogShellStar I

/-- Consumer: calibration p* is 5. -/
theorem consumer_calibration_pStar : (calibrationInvariantsData).pStar = 5 :=
  calibrationInvariantsData_pStar

#check consumer_target_kummerInclusion
#check consumer_target_logShell_eq
#check consumer_preLogShell_image
#check consumer_pStar
#check consumer_calibration_pStar

end LeanFormal.IUT.XiFPaper.Mzk1Prop58iConsumerChainActual
end
