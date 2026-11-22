/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # diagonal LinearEquiv bridge: exact GAP record (task-109)

The LinearEquiv route (`diagLinEquiv` with inverse `p^{-f_i}`) still hits
beta-reduction/inverse-law mismatches in the project Lean context; the
image bridge `diagEquivCLM '' coordLattice = coordDual` is not attempted.
This file records the gap.  No axiom/sorry. -/
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1DiagEquivBridgeActual
def diagBridgeRows : List (String × String) :=
  [ ("diagLinEquiv/ContinuousLinearEquiv", "GAP: inverse-law reduction"),
    ("image = coordDual", "GAP"),
    ("compact/open/positivity", "GAP") ]
theorem diagBridgeRows_length : diagBridgeRows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1DiagEquivBridgeActual
