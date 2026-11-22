import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
open LeanFormal.IUT
example : IsGalois ℚ GaussianField := by infer_instance
example : FiniteDimensional ℚ GaussianField := by infer_instance
example : Algebra.IsSeparable ℚ GaussianField := by infer_instance
example : Normal ℚ GaussianField := by infer_instance
