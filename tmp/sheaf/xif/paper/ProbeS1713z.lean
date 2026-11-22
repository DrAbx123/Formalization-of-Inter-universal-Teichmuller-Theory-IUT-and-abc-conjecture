import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import Mathlib.Tactic
open Polynomial
open WeierstrassCurve
open LeanFormal.IUT

example : (C (-1 : ZMod 5) : (ZMod 5)[X]) * C (-1) = 1 := by
  rw [← Polynomial.C_mul]
  have h : (-1 : ZMod 5) * (-1) = 1 := by decide
  rw [h]
  rfl

example : splitReductionPolynomial (WeierstrassCurve.mk (0 : ZMod 5) 4 0 0 0) = (X^2 + 1 : (ZMod 5)[X]) := by
  simp [splitReductionPolynomial, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  rw [show (4 : ZMod 5) = -1 by decide]
  have hsq : (C (-1 : ZMod 5) : (ZMod 5)[X]) * C (-1) = 1 := by
    rw [← Polynomial.C_mul]
    have h : (-1 : ZMod 5) * (-1) = 1 := by decide
    rw [h]
    rfl
  rw [hsq]
  ring
