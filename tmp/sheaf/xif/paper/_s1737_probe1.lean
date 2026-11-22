import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.CategoryTheory.Galois.Examples

noncomputable section
open CategoryTheory

namespace S1737Probe

variable (G : Type) [Group G]

example (X : Action FintypeCat.{0} G) : MulAction G X.V := inferInstance

example (X : Action FintypeCat.{0} G) : MulAction G ((Action.forget FintypeCat.{0} G).obj X) := by
  infer_instance

example (X : Action FintypeCat.{0} G) : MulAction G ((forget₂ (Action FintypeCat.{0} G) FintypeCat.{0}).obj X) := by
  infer_instance

end S1737Probe
