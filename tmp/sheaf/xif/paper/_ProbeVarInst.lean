import Mathlib

open MeasureTheory

universe u v
variable {ι : Type u} {α : ι → Type v}
variable [∀ i, MeasurableSpace (α i)]

#check fun (μ : ∀ i, Measure (α i)) => Measure.pi μ
