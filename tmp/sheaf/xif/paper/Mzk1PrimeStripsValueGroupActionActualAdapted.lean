/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Prime-strips: value-group integer action on exponent vectors -/

namespace LeanFormal.IUT.XiFPaper.PrimeStripsValueGroupActionActual

variable {ι : Type*}

abbrev ExpVec (ι : Type*) := ι → ℤ

/-- Additive action of an integer on an exponent vector (value-group scaling). -/
def vgAct (k : ℤ) (v : ExpVec ι) : ExpVec ι := fun i => v i + k

@[simp] theorem vgAct_apply (k : ℤ) (v : ExpVec ι) (i : ι) : vgAct k v i = v i + k := rfl

theorem vgAct_zero (v : ExpVec ι) : vgAct 0 v = v := by
  funext i
  simp [vgAct]

theorem vgAct_add (k l : ℤ) (v : ExpVec ι) :
    vgAct (k + l) v = vgAct k (vgAct l v) := by
  funext i
  simp [vgAct]
  ring

theorem vgAct_add' (k l : ℤ) (v : ExpVec ι) :
    vgAct k (vgAct l v) = vgAct l (vgAct k v) := by
  funext i
  simp [vgAct]
  ring

end LeanFormal.IUT.XiFPaper.PrimeStripsValueGroupActionActual
