/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Prime-strips (F/D): exponent-vector value group facts -/

namespace LeanFormal.IUT.XiFPaper.PrimeStripExponentActual

variable {ι : Type*}

/-- Exponent vector over a prime set (value-group element of a prime strip). -/
abbrev ExpVec (ι : Type*) := ι → ℤ

def evZero : ExpVec ι := fun _ => 0

def evAdd (a b : ExpVec ι) : ExpVec ι := fun i => a i + b i

def evNeg (a : ExpVec ι) : ExpVec ι := fun i => -a i

def evLE (a b : ExpVec ι) : Prop := ∀ i, a i ≤ b i

@[simp] theorem evAdd_apply (a b : ExpVec ι) (i : ι) : evAdd a b i = a i + b i := rfl

@[simp] theorem evZero_apply (i : ι) : (evZero : ExpVec ι) i = 0 := rfl

theorem evAdd_comm (a b : ExpVec ι) : evAdd a b = evAdd b a := by
  funext i
  simp [evAdd, add_comm]

theorem evAdd_assoc (a b c : ExpVec ι) :
    evAdd (evAdd a b) c = evAdd a (evAdd b c) := by
  funext i
  simp [evAdd, add_assoc]

theorem evAdd_zero (a : ExpVec ι) : evAdd a evZero = a := by
  funext i
  simp [evAdd]

theorem evZero_add (a : ExpVec ι) : evAdd evZero a = a := by
  funext i
  simp [evAdd]

theorem evAdd_neg (a : ExpVec ι) : evAdd a (evNeg a) = evZero := by
  funext i
  simp [evAdd, evNeg]

theorem evLE_refl (a : ExpVec ι) : evLE a a := fun _ => le_refl _

theorem evLE_trans {a b c : ExpVec ι} (hab : evLE a b) (hbc : evLE b c) : evLE a c :=
  fun i => le_trans (hab i) (hbc i)

theorem evLE_antisymm {a b : ExpVec ι} (hab : evLE a b) (hba : evLE b a) : a = b := by
  funext i
  exact le_antisymm (hab i) (hba i)

theorem evAdd_mono {a a' b b' : ExpVec ι} (ha : evLE a a') (hb : evLE b b') :
    evLE (evAdd a b) (evAdd a' b') := by
  intro i
  simp [evAdd]
  exact add_le_add (ha i) (hb i)

end LeanFormal.IUT.XiFPaper.PrimeStripExponentActual
