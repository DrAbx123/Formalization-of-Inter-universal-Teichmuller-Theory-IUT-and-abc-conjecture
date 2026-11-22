import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
open LeanFormal.IUT
open Polynomial
local instance factIrr : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
#check LeanFormal.IUT.IUTII.Frobenioid.Example36.gaussianField_finrank
noncomputable instance quad : Algebra.IsQuadraticExtension ℚ GaussianField where
  finrank_eq_two' := LeanFormal.IUT.IUTII.Frobenioid.Example36.gaussianField_finrank
example : IsGalois ℚ GaussianField := inferInstance
example : Normal ℚ GaussianField := inferInstance
