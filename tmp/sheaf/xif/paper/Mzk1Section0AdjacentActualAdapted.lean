/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Section 0: adjacent pairs on Z -/

namespace LeanFormal.IUT.XiFPaper.Section0AdjacentActual

def Adjacent (e e' : Int) : Prop := e' = e + 1

theorem adjacent_iff (e e' : Int) : Adjacent e e' ↔ e' = e + 1 := Iff.rfl

theorem adjacent_irrefl (e : Int) : ¬ Adjacent e e := by
  unfold Adjacent
  omega

theorem adjacent_functional {e e1 e2 : Int} (h1 : Adjacent e e1) (h2 : Adjacent e e2) :
    e1 = e2 := by
  unfold Adjacent at h1 h2
  omega

theorem adjacent_comp {e1 e2 e3 : Int} (h1 : Adjacent e1 e2) (h2 : Adjacent e2 e3) :
    e3 = e1 + 2 := by
  unfold Adjacent at h1 h2
  omega

theorem adjacent_succ (e : Int) : Adjacent e (e + 1) := rfl

end LeanFormal.IUT.XiFPaper.Section0AdjacentActual
