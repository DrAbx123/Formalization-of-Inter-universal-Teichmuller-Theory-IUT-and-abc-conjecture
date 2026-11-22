import Mathlib
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary

open LeanFormal.IUT
open NumberField

variable {l : PrimeGeFive} (S : SourceDefinition31Data l)

abbrev DivType (S : SourceDefinition31Data l) : Type := InfinitePlace S.arithmetic.F → ℤ

example : DivType S := 0
example (D : DivType S) : DivType S := -D
example (D E : DivType S) : DivType S := D + E
