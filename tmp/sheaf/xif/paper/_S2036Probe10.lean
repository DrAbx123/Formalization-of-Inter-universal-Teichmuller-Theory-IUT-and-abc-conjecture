import Mathlib.Tactic.Group

example {A : Type} [CommGroup A] (a b c d : A) :
    a * b * c * d⁻¹ * c⁻¹ * b⁻¹ = a * d⁻¹ := by
  simp [mul_comm, mul_left_comm, mul_assoc]

example {A : Type} [CommGroup A] (a b c d e : A) :
    a * b * c⁻¹ * d * c * e⁻¹ = d * a * b * e⁻¹ := by
  simp [mul_comm, mul_left_comm, mul_assoc]
