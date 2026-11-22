import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Normed.Field.Basic

#check @Module.toMulActionWithZero
#check @Module.toDistribMulAction
#check @Module.toMulAction

example (V : Type) [AddCommGroup V] (h : Module Real V) (a b : V) :
    (1:Real) • a + (0:Real) • b = a := by
  haveI := h
  haveI : MulActionWithZero Real V := Module.toMulActionWithZero
  rw [one_smul, zero_smul, add_zero]

example (V : Type) [AddCommGroup V] (h : Module Real V) (a b : V) : a ∈ segment Real a b := by
  haveI := h
  haveI : MulActionWithZero Real V := Module.toMulActionWithZero
  exact left_mem_segment Real a b

example (V : Type) [AddCommGroup V] (h : Module Real V) (a b : V) : b ∈ segment Real a b := by
  haveI := h
  haveI : MulActionWithZero Real V := Module.toMulActionWithZero
  exact right_mem_segment Real a b
