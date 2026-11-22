import Mathlib

open MeasureTheory

universe u v w
variable {ι : Type u} {α : ι → Type v}
variable [Fintype ι]
variable [instMS : ∀ i, MeasurableSpace (α i)]
variable [instB : ∀ i, BorelSpace (α i)]
variable (μ : ∀ i, Measure (α i))
variable [instH : ∀ i, Measure.IsAddHaarMeasure (μ i)]

#check fun (i : ι) => μ i
