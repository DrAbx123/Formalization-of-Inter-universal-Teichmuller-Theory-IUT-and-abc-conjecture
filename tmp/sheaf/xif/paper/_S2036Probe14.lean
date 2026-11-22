import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

example (h : (1 : ZMod 2) = 0) : False := by
  have h2 : (1 : ZMod 2) = 0 := by
    simpa using h
  exact one_ne_zero h2

example (h : (1 : ZMod 2) = 0) : False := by
  have h2 : (1 : ZMod 2) = 0 := h
  exact one_ne_zero h2
