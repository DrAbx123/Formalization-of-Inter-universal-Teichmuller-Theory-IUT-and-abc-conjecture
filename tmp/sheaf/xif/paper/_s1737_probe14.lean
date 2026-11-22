import Mathlib.CategoryTheory.Action.Concrete
import Mathlib.CategoryTheory.Action.Continuous
import Mathlib.Topology.Category.FinTopCat
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Separation.Basic
import Mathlib.GroupTheory.Index

noncomputable section
open CategoryTheory
open scoped FintypeCatDiscrete

namespace S1737Probe

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def S1737AllFiniteActionsContinuous : Prop :=
  ∀ X : Action FintypeCat.{0} G, Action.IsContinuous X

def S1737EveryFiniteIndexSubgroupOpen : Prop :=
  ∀ H : Subgroup G, H.FiniteIndex → IsOpen (H : Set G)

theorem allFiniteIndexOpen_of_allContinuous
    (h : S1737AllFiniteActionsContinuous G) (H : Subgroup G) [H.FiniteIndex] :
    IsOpen (H : Set G) := by
  letI : Fintype (G ⧸ H) := Subgroup.fintypeQuotientOfFiniteIndex
  let X : Action FintypeCat.{0} G := G ⧸ₐ H
  have hX : Action.IsContinuous X := h X
  have hX' : ContinuousSMul G X.V := hX
  let x0 : X.V := ((1 : G) : G ⧸ H)
  have hstab : IsOpen (MulAction.stabilizer G x0 : Set G) := by
    haveI : DiscreteTopology X.V := inferInstance
    exact stabilizer_isOpen G x0
  change IsOpen (MulAction.stabilizer G ((1 : G) : G ⧸ H) : Set G) at hstab
  rw [MulAction.stabilizer_quotient] at hstab
  exact hstab

theorem allContinuous_of_allFiniteIndexOpen
    (h : S1737EveryFiniteIndexSubgroupOpen G) :
    S1737AllFiniteActionsContinuous G := by
  intro X
  change ContinuousSMul G X.V
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro x
  haveI : Finite (G ⧸ MulAction.stabilizer G x) :=
    (Equiv.finite_iff (MulAction.orbitEquivQuotientStabilizer G x)).mp inferInstance
  exact h (MulAction.stabilizer G x) (Subgroup.finiteIndex_of_finite_quotient)

theorem allContinuous_iff_allFiniteIndexOpen :
    S1737AllFiniteActionsContinuous G ↔ S1737EveryFiniteIndexSubgroupOpen G :=
  ⟨fun h H hH => allFiniteIndexOpen_of_allContinuous G h H,
   allContinuous_of_allFiniteIndexOpen G⟩

end S1737Probe
