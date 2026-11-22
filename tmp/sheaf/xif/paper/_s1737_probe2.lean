import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.CategoryTheory.Galois.Examples

noncomputable section
open CategoryTheory

namespace S1737Probe

variable (G : Type) [Group G]

example (X : Action FintypeCat.{0} G) : MulAction G X.V := inferInstance

example (X : Action FintypeCat.{0} G) : (Action.forget FintypeCat.{0} G).obj X = X.V := rfl

example (X : Action FintypeCat.{0} G) : MulAction G ((Action.forget FintypeCat.{0} G).obj X).obj := by
  change MulAction G X.V
  infer_instance

example (X : Action FintypeCat.{0} G) : MulAction G ((Action.forget FintypeCat.{0} G).obj X).obj := by
  haveI : MulAction G X.V := inferInstance
  exact (inferInstance : MulAction G X.V)

end S1737Probe
