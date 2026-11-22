import tmp.sheaf.xif.paper.S63OBoundaryLogShellActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)
example (x : CompletionIntegers place.val) : Valued.v x.1 ≤ 1 := x.2
example (x : CompletionIntegers place.val) : ‖x.1‖ ≤ 1 := by
  exact (Valued.toNormedField.norm_le_one_iff).mpr x.2
