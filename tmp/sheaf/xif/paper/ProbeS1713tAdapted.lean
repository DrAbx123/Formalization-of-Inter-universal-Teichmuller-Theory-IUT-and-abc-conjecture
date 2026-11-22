import LeanFormal.IUT.ABCBridge.Geometry.FreySplitMultiplicativeReduction
set_option maxHeartbeats 1000000
open Polynomial
open LeanFormal.IUT

example : (2 : ZMod 5) ^ 2 = (-1 : ZMod 5) := by decide

example : (X^2 - C (-1) : (ZMod 5)[X]).Splits :=
  (frey_quadratic_splits_iff_exists_square (-1)).2 ⟨2, by decide⟩

example : (X^2 + 1 : (ZMod 5)[X]) = (X^2 - C (-1) : (ZMod 5)[X]) := by
  have hC : C (-1 : ZMod 5) = (-1 : (ZMod 5)[X]) := by simp
  rw [hC]
  ring
