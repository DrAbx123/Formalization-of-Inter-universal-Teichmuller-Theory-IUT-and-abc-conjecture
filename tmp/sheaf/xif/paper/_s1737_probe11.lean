import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.Topology.Category.FinTopCat
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Separation.Basic

noncomputable section
open CategoryTheory
open scoped FintypeCatDiscrete

namespace S1737Probe

def AllFiniteActionsContinuous (G : Type) [Group G] [TopologicalSpace G] : Prop :=
  ∀ X : Action FintypeCat.{0} G, Action.IsContinuous X

theorem allFiniteActionsContinuous_of_finite
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Finite G] [T1Space G] :
    AllFiniteActionsContinuous G := by
  intro X
  change ContinuousSMul G X.V
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  exact isOpen_discrete _

end S1737Probe
