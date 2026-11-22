import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import Mathlib.Tactic
open Polynomial
open WeierstrassCurve
open LeanFormal.IUT

example : splitReductionPolynomial (WeierstrassCurve.mk (0 : ZMod 5) 4 0 0 0) = (X^2 + 1 : (ZMod 5)[X]) := by
  simp [splitReductionPolynomial, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  rw [show (4 : ZMod 5) = -1 by decide]
  ring
