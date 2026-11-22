import Mathlib
noncomputable section
namespace ProbeStruct
structure R where
  J : Type
  [fintypeJ : Fintype J]
  E : J → Type
  [normedField : ∀ j, NontriviallyNormedField (E j)]
  [measurableSpace : MeasurableSpace ((j : J) → E j)]
  x : (j : J) → E j
end ProbeStruct
