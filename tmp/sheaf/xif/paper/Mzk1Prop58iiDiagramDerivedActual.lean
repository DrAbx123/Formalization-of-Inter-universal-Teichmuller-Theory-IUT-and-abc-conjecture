import tmp.sheaf.xif.paper.Mzk1Prop58iiDiagramActual
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellAbsTopIIIBridge

/-!
# Mzk1Prop58iiDiagramDerivedActual — derived vertex-inclusion laws for the concrete
Gamma^x_non model (new theorems from the existing NonDiagramModel asset + bridge).
No copies/bookkeeping; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Prop58iiDiagramDerivedActual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iiDiagramActual

universe u

/-- Derived: under the bridge, the unit-image vertex equals the invariant-image vertex. -/
theorem diagram_unitImage_eq_invariantImage (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) :
    (nonDiagramModel D).unitImage = (nonDiagramModel D).invariantImage := by
  unfold NonDiagramModel.unitImage NonDiagramModel.invariantImage
  exact h

/-- Derived: under the bridge, the invariant-image vertex lies in the log-shell vertex. -/
theorem diagram_invariantImage_subset_logShell (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) :
    (nonDiagramModel D).invariantImage ⊆ (nonDiagramModel D).logShellSet := by
  intro a ha
  unfold NonDiagramModel.invariantImage at ha
  unfold NonDiagramModel.logShellSet
  exact D.codomainKummerContained_of_invariantImageIdentification h (h ▸ ha)

/-- Derived: under the bridge, the log-shell vertex equals the inv-scaled unit vertex. -/
theorem diagram_logShell_eq_invScaled (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) :
    (nonDiagramModel D).logShellSet = (nonDiagramModel D).invScaledUnitImage := by
  unfold NonDiagramModel.logShellSet NonDiagramModel.invScaledUnitImage
  exact D.logShell_eq_invScaledUnitLayer_of_invariantImageIdentification h

/-- Derived: the invariant-image vertex is always inside the unit-image vertex. -/
theorem diagram_invariantImage_subset_unitImage (D : SourceLogShellDatum.{u}) :
    (nonDiagramModel D).invariantImage ⊆ (nonDiagramModel D).unitImage := by
  intro a ha
  unfold NonDiagramModel.invariantImage at ha
  unfold NonDiagramModel.unitImage
  exact D.preLogShell_subset_unitLayer ha

#check diagram_unitImage_eq_invariantImage
#check diagram_invariantImage_subset_logShell
#check diagram_logShell_eq_invScaled
#check diagram_invariantImage_subset_unitImage

end LeanFormal.IUT.XiFPaper.Mzk1Prop58iiDiagramDerivedActual
end
