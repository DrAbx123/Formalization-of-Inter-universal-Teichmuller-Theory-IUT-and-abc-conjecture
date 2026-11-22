import Mathlib.Tactic
open Polynomial

example : (1 : ZMod 5) = -4 := by
  have h : (4 : ZMod 5) = -1 := by decide
  rw [show (-4 : ZMod 5) = -(4 : ZMod 5) by rfl, h]
  ring

example : (1 : (ZMod 5)[X]) = -4 := by
  have h1 : (1 : ZMod 5) = -4 := by
    have h : (4 : ZMod 5) = -1 := by decide
    rw [show (-4 : ZMod 5) = -(4 : ZMod 5) by rfl, h]
    ring
  calc (1 : (ZMod 5)[X]) = C (1 : ZMod 5) := rfl
    _ = C (-4 : ZMod 5) := by rw [h1]
    _ = -4 := by rw [Polynomial.C_neg, Polynomial.C_ofNat]

example : (X^2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X + C 2) := by
  simp only [Polynomial.C_ofNat]
  ring_nf
  have h1 : (1 : ZMod 5) = -4 := by
    have h : (4 : ZMod 5) = -1 := by decide
    rw [show (-4 : ZMod 5) = -(4 : ZMod 5) by rfl, h]
    ring
  have hpoly : (1 : (ZMod 5)[X]) = -4 := by
    calc (1 : (ZMod 5)[X]) = C (1 : ZMod 5) := rfl
      _ = C (-4 : ZMod 5) := by rw [h1]
      _ = -4 := by rw [Polynomial.C_neg, Polynomial.C_ofNat]
  rw [hpoly]
