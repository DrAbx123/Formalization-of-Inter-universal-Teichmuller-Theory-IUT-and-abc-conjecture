import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import Mathlib.Tactic
open Polynomial
open WeierstrassCurve
open LeanFormal.IUT

example : splitReductionPolynomial (WeierstrassCurve.mk (0 : ZMod 5) 4 0 0 0) = (X^2 + 1 : (ZMod 5)[X]) := by
  simp [splitReductionPolynomial, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  rw [show (4 : ZMod 5) = -1 by decide]
  simp only [← Polynomial.C_pow]
  have h4 : ((-1 : ZMod 5) ^ 4) = 1 := by decide
  have h5 : ((-1 : ZMod 5) ^ 5) = -1 := by decide
  rw [h4, h5]
  rw [show C (1 : ZMod 5) = (1 : (ZMod 5)[X]) by simp,
      show C (-1 : ZMod 5) = (-1 : (ZMod 5)[X]) by simp]
  ring
