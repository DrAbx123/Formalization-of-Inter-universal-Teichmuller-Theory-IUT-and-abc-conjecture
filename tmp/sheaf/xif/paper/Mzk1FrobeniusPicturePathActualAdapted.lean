/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Mathlib

/-! # Frobenius-picture Gamma: vertex chains (Section 0 linear oriented graph) -/

namespace LeanFormal.IUT.XiFPaper.FrobeniusPicturePathActual

def gammaArrow (n m : Int) : Prop := m = n + 1

theorem gammaArrow_iff (n m : Int) : gammaArrow n m ↔ m = n + 1 := Iff.rfl

/-- The k-th vertex of the chain starting at n. -/
def chainVertex (n : Int) : Nat → Int
  | 0 => n
  | k + 1 => chainVertex n k + 1

theorem chainVertex_succ (n : Int) (k : Nat) :
    chainVertex n (k + 1) = chainVertex n k + 1 := rfl

theorem chainVertex_eq (n : Int) (k : Nat) : chainVertex n k = n + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [chainVertex_succ, ih]
      push_cast
      ring

theorem chainVertex_arrow (n : Int) (k : Nat) :
    gammaArrow (chainVertex n k) (chainVertex n (k + 1)) := by
  unfold gammaArrow
  rw [chainVertex_succ]

theorem chainVertex_strictMono (n : Int) : StrictMono (chainVertex n) := by
  intro a b hab
  rw [chainVertex_eq, chainVertex_eq]
  omega

end LeanFormal.IUT.XiFPaper.FrobeniusPicturePathActual
