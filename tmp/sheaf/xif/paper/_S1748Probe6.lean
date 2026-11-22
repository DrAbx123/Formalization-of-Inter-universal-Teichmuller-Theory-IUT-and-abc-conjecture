import Mathlib.FieldTheory.SeparableClosure

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

example (x y : Ω) : x ∈ IntermediateField.adjoin K ({x, y} : Set Ω) :=
  IntermediateField.subset_adjoin K (by simp : x ∈ ({x, y} : Set Ω))

example (x y : Ω) : y ∈ IntermediateField.adjoin K ({x, y} : Set Ω) :=
  IntermediateField.subset_adjoin K (by simp : y ∈ ({x, y} : Set Ω))
