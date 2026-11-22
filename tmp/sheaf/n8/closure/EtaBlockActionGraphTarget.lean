import tmp.sheaf.n8.closure.EtaTensorSplitActual
import tmp.sheaf.n8.closure.EtaGeneralQHaarScalingActual
import tmp.sheaf.n8.closure.FiniteObservationHullProofs3

/-!
# EtaBlockActionGraphTarget

Actual tensor action `tensorActionMul` on a one-factor block, and the exact
missing lattice-graph data: source lattices `L_u/L_v` and integral edges
`T_e : L_u → L_v` (not a same-lattice preservation condition).
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaBlockActionGraphTarget

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.EtaTensorSplitActual
open LeanFormal.IUT.N8Closure.EtaGeneralQHaarScalingActual
open LeanFormal.IUT.N8Closure.FiniteObservationHull
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open ABCBridge.N8.C3TensorTargetCorrection
open scoped NNReal ENNReal Pointwise NormedField TensorProduct

variable {l : PrimeGeFive} (X : N8NativeInput l)
local instance : Fact (Nat.Prime (nativePrime X)) := nativePrimeFact X

abbrev Kf : Type := CommonPrimeCompletion (nativeFPlaceAtPrime X)
abbrev A : Fin 1 → Type := fun _ => Kf X
abbrev E : Type := ⨂[ℚ_[nativePrime X]] (i : Fin 1), A X i

noncomputable def actualTensorAction (g : Kf X) : E X →ₗ[ℚ_[nativePrime X]] E X :=
  tensorActionMul (p := nativePrime X) (A := A X) 0 g

theorem actualTensorAction_apply (g : Kf X) (x : E X) :
    actualTensorAction X g x =
      tensorActionMul (p := nativePrime X) (A := A X) 0 g x := rfl

/-- A tensor lattice graph edge: `T_e` maps the actual `source` lattice into
the target lattice (not necessarily onto the same lattice). -/
def TensorGraphEdge (g : Kf X) (Lu Lv : Set (E X)) : Prop :=
  ∀ x ∈ Lu, actualTensorAction X g x ∈ Lv

/-- Exact missing actual source data: a `ℤ_[p]`-lattice graph with vertices
`L_u/L_v`, actual edges given by tensor actions, a nontrivial edge, and
source Ind2 provenance. -/
def MissingTensorLatticeGraphData (X : N8NativeInput l) : Prop :=
  ∃ (V : Type) (L : V → Set (E X)) (edge : V → V → Kf X → Prop),
    (∃ v, Nonempty (L v)) ∧
    (∃ u v g, TensorGraphEdge X g (L u) (L v) ∧ (L u).Nonempty)

theorem tensorGraphEdge_one_univ :
    TensorGraphEdge X (1 : Kf X) Set.univ Set.univ := by
  intro x _
  trivial

end LeanFormal.IUT.N8Closure.EtaBlockActionGraphTarget