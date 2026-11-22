import LeanFormal.IUT.IUTII.Kummer.SourceLogShellAbsTopIIIBridge
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier

/-!
# Mzk1LogShellBridgeDerived2Actual — derived membership/inclusion laws under the AbsTopIII
invariant-image bridge (new theorems from existing tree bridge assets; no copies).
No axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LogShellBridgeDerived2Actual

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum

universe u

/-- Derived: under the bridge, log-shell membership is p*-scaled unit-layer membership. -/
theorem logShell_mem_iff_scaled_unitLayer (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) (a : D.K) :
    a ∈ D.logShell ↔ (D.pStar : D.K) * a ∈ D.unitLayer := by
  change (D.pStar : D.K) * a ∈ D.preLogShell ↔ (D.pStar : D.K) * a ∈ D.unitLayer
  rw [h]
  exact Iff.rfl

/-- Derived: under the bridge, the unit layer is contained in the log-shell. -/
theorem unitLayer_subset_logShell_of_bridge (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) : D.unitLayer ⊆ D.logShell :=
  D.codomainKummerContained_of_invariantImageIdentification h

/-- Derived: under the bridge, the pre-log-shell is contained in the log-shell. -/
theorem preLogShell_subset_logShell_of_bridge (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) : D.preLogShell ⊆ D.logShell := by
  rw [← h]
  exact unitLayer_subset_logShell_of_bridge D h

/-- Derived: under the bridge, the inv-scaled unit layer equals the log-shell. -/
theorem invScaledUnitLayer_eq_logShell (D : SourceLogShellDatum.{u})
    (h : SourceLogShellInvariantImageIdentification D) :
    D.invScaledUnitLayer = D.logShell :=
  (D.logShell_eq_invScaledUnitLayer_of_invariantImageIdentification h).symm

/-- Derived: the bridge hypothesis is equivalent to unit-layer containment in pre-log-shell. -/
theorem bridge_iff_unitLayer_subset (D : SourceLogShellDatum.{u}) :
    SourceLogShellInvariantImageIdentification D ↔ D.unitLayer ⊆ D.preLogShell :=
  D.invariantImageIdentification_iff_unitLayer_subset

#check logShell_mem_iff_scaled_unitLayer
#check unitLayer_subset_logShell_of_bridge
#check preLogShell_subset_logShell_of_bridge
#check invScaledUnitLayer_eq_logShell
#check bridge_iff_unitLayer_subset

end LeanFormal.IUT.XiFPaper.Mzk1LogShellBridgeDerived2Actual
end
