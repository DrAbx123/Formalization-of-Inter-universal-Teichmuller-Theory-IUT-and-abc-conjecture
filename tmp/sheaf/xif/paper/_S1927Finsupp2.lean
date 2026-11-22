import Mathlib.Data.NNReal.Basic
import Mathlib.Data.Finsupp.Basic

set_option pp.all true

example {X : Type} (b c : X →₀ NNReal) (h : b = c) : b = c := by
  ext v
  trace_state
  exact congrFun (congrArg DFunLike.coe h) v
