import Mathlib
noncomputable section
namespace ProbeStruct
variable {ι : Type} [Fintype ι] (A : ι → Type) [∀ i, NormedField (A i)]
structure R where
  J : Type
  [fintypeJ : Fintype J]
  E : J → Type
  [normedField : ∀ j, NontriviallyNormedField (E j)]
  [normedAlgebra : ∀ j, NormedAlgebra ℚ_[2] (E j)]
  [finiteDimensional : ∀ j, FiniteDimensional ℚ_[2] (E j)]
  [properSpace : ∀ j, ProperSpace (E j)]
  equiv : ((j : J) → E j)
end ProbeStruct
