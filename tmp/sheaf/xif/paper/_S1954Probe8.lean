import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Normed.Field.Basic

open scoped Classical

#synth MulAction Real Complex
#synth MulActionWithZero Real Complex

example (V : Type) [AddCommGroup V] [Module Real V] (a b : V) : (1:Real) • a + (0:Real) • b = a := by
  rw [one_smul, zero_smul, add_zero]

example (V : Type) [AddCommGroup V] (h : Module Real V) (a b : V) : (1:Real) • a + (0:Real) • b = a := by
  haveI := h
  rw [one_smul, zero_smul, add_zero]

example (V : Type) [AddCommGroup V] (h : Module Real V) (a b : V) : a ∈ segment Real a b := by
  haveI := h
  exact left_mem_segment Real a b

example (V : Type) [AddCommGroup V] (h : Module Real V) (a b : V) : b ∈ segment Real a b := by
  haveI := h
  exact right_mem_segment Real a b
