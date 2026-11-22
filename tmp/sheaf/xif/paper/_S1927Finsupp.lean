import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Finsupp.Basic

example {X : Type} (a b c : X →₀ NNReal) (h : a + b = a + c) : b = c := by
  ext v
  have hv := congrArg (fun g : X →₀ NNReal => g v) h
  simp only [Finsupp.add_apply] at hv
  trace_state
  exact add_left_cancel hv
