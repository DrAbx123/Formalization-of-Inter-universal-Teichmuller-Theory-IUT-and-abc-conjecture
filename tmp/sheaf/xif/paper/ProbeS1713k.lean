import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import Mathlib.Tactic
open Polynomial
open WeierstrassCurve
open LeanFormal.IUT

lemma splitReductionPolynomial_mk_zero {R : Type*} [CommRing R] (a2 a4 : R) :
    splitReductionPolynomial (WeierstrassCurve.mk 0 a2 0 a4 0) =
      C (16 * a2 ^ 2 - 48 * a4) * X ^ 2 - C (16 * a2 ^ 3 - 72 * a2 * a4) := by
  simp [splitReductionPolynomial, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.c₄]
  ring

example : splitReductionPolynomial (WeierstrassCurve.mk (0 : ZMod 5) 4 0 0 0) =
    (X^2 + 1 : (ZMod 5)[X]) := by
  rw [splitReductionPolynomial_mk_zero]
  have hc : (16 * 4 ^ 2 - 48 * 0 : ZMod 5) = 1 := by decide
  have hd : (16 * 4 ^ 3 - 72 * 4 * 0 : ZMod 5) = 4 := by decide
  rw [hc, hd]
  have h4 : (4 : ZMod 5) = -1 := by decide
  rw [h4]
  ring

example : (X^2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X + C 2) := by
  have h : (2 : ZMod 5) * 2 = -1 := by decide
  calc (X^2 + 1 : (ZMod 5)[X]) = X^2 - C ((2 : ZMod 5) * 2) := by rw [h]; ring
    _ = (X - C 2) * (X + C 2) := by ring

example : (X^2 + 1 : (ZMod 5)[X]).Splits := by
  rw [show (X^2 + 1 : (ZMod 5)[X]) = (X - C 2) * (X + C 2) by
    have h : (2 : ZMod 5) * 2 = -1 := by decide
    calc (X^2 + 1 : (ZMod 5)[X]) = X^2 - C ((2 : ZMod 5) * 2) := by rw [h]; ring
      _ = (X - C 2) * (X + C 2) := by ring]
  exact (Polynomial.Splits.X_sub_C 2).mul (Polynomial.Splits.X_add_C 2)
