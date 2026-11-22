/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Log-shell invariants: carrier/invariant-image interface (real containment laws) -/

namespace LeanFormal.IUT.XiFPaper.LogShellInvariantActual

/-- A log-shell carrier: a set of integers containing 0. -/
structure LogShellCarrier where
  carrier : Set Int
  zero_mem : 0 ∈ carrier

/-- Invariant-image data: unit layer and log image inside the carrier, with the
log image closed under addition (the image of the log map is a subgroup). -/
structure LogShellInvariant where
  carrier : Set Int
  unitLayer : Set Int
  logImage : Set Int
  unit_subset : unitLayer ⊆ carrier
  log_subset : logImage ⊆ carrier
  zero_logImage : 0 ∈ logImage
  logImage_add : ∀ x y : Int, x ∈ logImage → y ∈ logImage → x + y ∈ logImage

theorem LogShellInvariant.zero_mem_carrier (D : LogShellInvariant) : 0 ∈ D.carrier :=
  D.log_subset D.zero_logImage

theorem LogShellInvariant.mem_carrier_of_mem_logImage (D : LogShellInvariant) {x : Int}
    (h : x ∈ D.logImage) : x ∈ D.carrier := D.log_subset h

theorem LogShellInvariant.mem_carrier_of_mem_unitLayer (D : LogShellInvariant) {x : Int}
    (h : x ∈ D.unitLayer) : x ∈ D.carrier := D.unit_subset h

theorem LogShellInvariant.add_mem_logImage (D : LogShellInvariant) {x y : Int}
    (hx : x ∈ D.logImage) (hy : y ∈ D.logImage) : x + y ∈ D.logImage :=
  D.logImage_add x y hx hy

end LeanFormal.IUT.XiFPaper.LogShellInvariantActual
