import Mathlib
noncomputable section
open MeasureTheory
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
  [measurableSpace : MeasurableSpace ((j : J) → E j)]
  [borelSpace : BorelSpace ((j : J) → E j)]
  equiv : (⨂[ℚ_[2]] i, A i) ≃ₐ[ℚ_[2]] ((j : J) → E j)
  lam : (j : J) → E j
  lam_ne_zero : ∀ j, lam j ≠ 0
  hull_pos : 0 < Measure.addHaar (Set.univ : Set ((j : J) → E j))
end ProbeStruct
