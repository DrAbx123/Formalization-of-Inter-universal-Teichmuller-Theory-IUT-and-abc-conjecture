import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! # S970: finite log-shell quotient carrier

FinalL is an algebraic closure, not finite-dimensional, and has no Mathlib
locally compact/Haar instance.  The paper tensor packets are finite-dimensional
log-shell subspaces/quotients.  This file records the finite carrier
Fin d -> Qp, its actual topology/topological additive group, and the exact
Haar/log-volume datum still needed.  No LocallyCompactSpace for FinalL is faked. -/

noncomputable section
open scoped BigOperators TensorProduct
open MeasureTheory
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S970FiniteLogShellCarrierActual

variable {p : Nat} [Fact p.Prime]

/-- The finite-dimensional p-adic log-shell quotient model. -/
abbrev FiniteLogShellCarrier (p : Nat) [Fact p.Prime] (d : Nat) : Type :=
  Fin d → ℚ_[p]

instance finiteLogShellAddCommGroup (d : Nat) :
    AddCommGroup (FiniteLogShellCarrier p d) := inferInstance

instance finiteLogShellTopologicalSpace (d : Nat) :
    TopologicalSpace (FiniteLogShellCarrier p d) := inferInstance

instance finiteLogShellIsTopologicalAddGroup (d : Nat) :
    IsTopologicalAddGroup (FiniteLogShellCarrier p d) := inferInstance

/-- Exact Haar/log-volume datum on the finite carrier.  All analytic instances
are explicit fields; none is asserted globally. -/
structure FiniteLogShellHaarData (d : Nat) where
  [locallyCompactSpace : LocallyCompactSpace (FiniteLogShellCarrier p d)]
  [measurableSpace : MeasurableSpace (FiniteLogShellCarrier p d)]
  [borelSpace : BorelSpace (FiniteLogShellCarrier p d)]
  measure : Measure (FiniteLogShellCarrier p d)
  [isAddHaar : Measure.IsAddHaarMeasure measure]
  unitRegion : Set (FiniteLogShellCarrier p d)
  unit_pos : 0 < measure unitRegion
  unit_lt_top : measure unitRegion < ⊤

/-- Exact required Haar datum on the finite quotient. -/
def FiniteLogShellHaarRequired (d : Nat) : Prop :=
  Nonempty (FiniteLogShellHaarData (p := p) d)

/-- Exact missing bridge: the actual paper tensor packet is Qp-linearly
equivalent to this finite carrier. -/
def FiniteQuotientBridge
    (Packet : Type) [AddCommGroup Packet] [Module ℚ_[p] Packet] : Prop :=
  ∃ d : Nat, Nonempty (Packet ≃ₗ[ℚ_[p]] FiniteLogShellCarrier p d)

end LeanFormal.IUT.XiFPaper.S970FiniteLogShellCarrierActual
end