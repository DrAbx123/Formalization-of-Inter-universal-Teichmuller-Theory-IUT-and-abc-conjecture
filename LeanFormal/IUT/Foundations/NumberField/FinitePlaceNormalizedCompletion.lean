import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion

/-!
# Compatibility module

This module is a pure import shim at the historical module path
LeanFormal.IUT.Foundations.NumberField.FinitePlaceNormalizedCompletion.
The source implementation moved to
LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedCompletion, but some
locally built oleans still list the historical module name as a dependency.
The shim contains no declarations, no axioms and no proofs; it only restores
module resolution for the existing lake state.
-/
