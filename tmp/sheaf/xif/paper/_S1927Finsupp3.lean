import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Finsupp.Basic

example {X : Type} (b c : X →₀ NNReal) (h : b = c) : b = c := by
  apply Finsupp.ext
  intro v
  trace_state
  exact congrFun (congrArg DFunLike.coe h) v
