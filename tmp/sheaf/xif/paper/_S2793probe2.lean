import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
open LeanFormal.IUT
open Polynomial
local instance factIrr : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
example : Field GaussianField := inferInstance
example : FiniteDimensional ℚ GaussianField := inferInstance
example : IsGalois GaussianField GaussianField := inferInstance
example : IsGalois ℚ GaussianField := inferInstance
example : Algebra.IsSeparable ℚ GaussianField := inferInstance
example : Normal ℚ GaussianField := inferInstance
