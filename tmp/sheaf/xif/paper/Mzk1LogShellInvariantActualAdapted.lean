/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Log-shell invariants: abstract carrier/invariant-image interface -/

namespace LeanFormal.IUT.XiFPaper.LogShellInvariantActual

structure LogShellCarrier where
  Carrier : Type
  zero_mem : (0 : Int) ∈ (Set.univ : Set Int)

/-- Invariant-image data: a subgroup of the carrier with a unit layer and log image. -/
structure LogShellInvariant where
  carrier : Set Int
  unitLayer : Set Int
  logImage : Set Int
  zero_mem : 0 ∈ carrier
  log_subset : logImage ⊆ carrier
  unit_subset : unitLayer ⊆ carrier

theorem zero_mem_carrier (D : LogShellInvariant) : 0 ∈ D.carrier := D.zero_mem

theorem logImage_subset_carrier (D : LogShellInvariant) : D.logImage ⊆ D.carrier :=
  D.log_subset

theorem unitLayer_subset_carrier (D : LogShellInvariant) : D.unitLayer ⊆ D.carrier :=
  D.unit_subset

theorem mem_carrier_of_mem_logImage (D : LogShellInvariant) {x : Int}
    (h : x ∈ D.logImage) : x ∈ D.carrier := D.log_subset h

end LeanFormal.IUT.XiFPaper.LogShellInvariantActual
