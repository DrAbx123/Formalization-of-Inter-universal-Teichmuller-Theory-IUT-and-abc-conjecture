import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.NumberTheory.NumberField.Basic

noncomputable section
open Polynomial

def H : ℚ[X] := 463856467968 * X ^ 6 + 3973952045056 * X ^ 4 + 1991485440000 * X ^ 2 + 6153500390625

abbrev F := Polynomial.SplittingField H

instance : NumberField F where
  to_charZero := inferInstance
  to_finiteDimensional := by
    letI : IsSplittingField ℚ F H := Polynomial.IsSplittingField.splittingField H
    exact Polynomial.IsSplittingField.finiteDimensional F H

example : NumberField F := inferInstance
#check Polynomial.nodup_roots
