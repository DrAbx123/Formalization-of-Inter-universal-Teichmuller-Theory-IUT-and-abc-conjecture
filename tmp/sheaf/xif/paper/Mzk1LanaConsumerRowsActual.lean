/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.external.ported.lana.Iut.Implication.LogVolumeBound
import tmp.external.ported.lana.Iut.Concrete.LocalEstimate
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A726 lana consumer rows (mainline): rhs_le / localEstimate usage

Direct consumers of the (U)-chain results, written WITHOUT named structures:
* `lana_rhs_le`: `LocalEstimate.rhs_le` (LogVolumeBound.lean:210) for arbitrary data;
* `lana_localEstimate`: the concrete `TowerArithmetic.localEstimate`
  (Concrete/LocalEstimate.lean:460);
* `lana_rhs_le_concrete`: the two composed on the concrete theta-pilot region.

PENDING-EXTERNAL: the lana tree is not compiled yet, so this file cannot compile
until the imported modules have oleans; it is ready to be used immediately after.
ABC gate NOT passed; no canonical change. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Mzk1LanaConsumerRowsActual

universe u

/-- `LocalEstimate.rhs_le`: the RHS log-volume bound of Steps (iv)-(vii). -/
theorem lana_rhs_le {X : Iut.Corollary312VariantData.{u}}
    (inv : Iut.Theorem110Invariants X) (est : inv.LocalEstimate) :
    X.rhsData.rhs ≤
      (∑ i, (∑ p ∈ inv.dst,
          inv.capsuleBound (X.rhsData.container.proc.capsule i).card p +
          (X.rhsData.container.proc.capsule i).card * Real.log (Real.sqrt 2 * Real.pi))) /
        X.rhsData.container.proc.length := 
  Iut.Theorem110Invariants.LocalEstimate.rhs_le inv est

/-- The concrete local estimates (`TowerArithmetic.localEstimate`). -/
theorem lana_localEstimate {D : Iut.InitialThetaData.{u}} (TA : Iut.TowerArithmetic D) :
    (D.invariants).LocalEstimate := 
  Iut.TowerArithmetic.localEstimate (D := D) TA

/-- Composed consumer: concrete theta-pilot local estimates give the RHS bound. -/
theorem lana_rhs_le_concrete {D : Iut.InitialThetaData.{u}} (TA : Iut.TowerArithmetic D) :
    (D.invariants).rhsData.rhs ≤
      (∑ i, (∑ p ∈ D.invariants.dst,
          D.invariants.capsuleBound
            (D.invariants.rhsData.container.proc.capsule i).card p +
          (D.invariants.rhsData.container.proc.capsule i).card *
            Real.log (Real.sqrt 2 * Real.pi))) /
        D.invariants.rhsData.container.proc.length := 
  lana_rhs_le D.invariants (lana_localEstimate TA)

/-- Pending-external status rows. -/
def consumerRows : List (String × String) :=
  [ ("rhs_le", "LocalEstimate.rhs_le (LogVolumeBound.lean:210) - consumer written"),
    ("localEstimate", "TowerArithmetic.localEstimate (Concrete/LocalEstimate.lean:460) - consumer written"),
    ("composed bound", "lana_rhs_le_concrete - consumer written"),
    ("pending external", "lana tree oleans not built yet; file ready (no named structure)"),
    ("scope", "ABC gate NOT passed; no canonical change") ]

theorem consumerRows_length : consumerRows.length = 5 := rfl

end Mzk1LanaConsumerRowsActual

end

/-! ### Axiom gates (top level) -/

#print axioms Mzk1LanaConsumerRowsActual.lana_rhs_le
#print axioms Mzk1LanaConsumerRowsActual.lana_localEstimate
#print axioms Mzk1LanaConsumerRowsActual.consumerRows_length