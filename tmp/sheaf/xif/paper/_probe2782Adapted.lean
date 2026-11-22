import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
open Polynomial
example : (AdjoinRoot.of (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) 37 = (37 : LeanFormal.IUT.GaussianField) :=
  map_natCast _ 37
example : (algebraMap ℚ LeanFormal.IUT.GaussianField) 37 = (37 : LeanFormal.IUT.GaussianField) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact map_natCast _ 37
