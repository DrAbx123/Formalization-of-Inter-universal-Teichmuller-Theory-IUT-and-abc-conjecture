import Mathlib.CategoryTheory.Galois.Examples
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.Topology.Category.FinTopCat
import Mathlib.GroupTheory.Index
import Iut.Foundations.SourceContinuousAnabelioid

noncomputable section
open CategoryTheory
open scoped FintypeCatDiscrete

namespace S1737Probe

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def AllFiniteActionsContinuous : Prop :=
  ∀ X : Action FintypeCat.{0} G, Action.IsContinuous X

def EveryFiniteIndexSubgroupOpen : Prop :=
  ∀ H : Subgroup G, H.FiniteIndex → IsOpen (H : Set G)

theorem allFiniteActionsContinuous_iff_finiteIndexOpen :
    AllFiniteActionsContinuous G ↔ EveryFiniteIndexSubgroupOpen G := by
  constructor
  · intro h H hH
    letI : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
    let X : Action FintypeCat.{0} G := Action.FintypeCat.ofMulAction G (FintypeCat.of (G ⧸ H))
    have hX : Action.IsContinuous X := h X
    have hstab : IsOpen (MulAction.stabilizer G ((1 : G) : G ⧸ H) : Set G) := by
      haveI : DiscreteTopology (G ⧸ H) := inferInstanceAs (DiscreteTopology X.V)
      have hX' : ContinuousSMul G X.V := hX
      have h1 : ((1 : G) : G ⧸ H) = ((1 : G) : X.V) := rfl
      rw [h1]
      exact stabilizer_isOpen G ((1 : G) : X.V)
    simpa [MulAction.stabilizer_quotient] using hstab
  · intro h X
    change ContinuousSMul G X.V
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    haveI : Finite (G ⧸ MulAction.stabilizer G x) :=
      (Equiv.finite_iff (MulAction.orbitEquivQuotientStabilizer G x)).mp inferInstance
    exact h (MulAction.stabilizer G x) (Subgroup.finiteIndex_of_finite_quotient)

end S1737Probe
