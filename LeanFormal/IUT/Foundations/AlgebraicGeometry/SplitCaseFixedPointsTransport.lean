import Mathlib.RingTheory.Invariant.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Transport of fixed points along a G-equivariant algebra equivalence

If `e : A ≃ₐ[S] B` intertwines the `G`-actions, then it restricts to an
`S`-algebra equivalence of the fixed-point subalgebras.  This is the base
transport used by the global CRT assembly.
-/
namespace ABCBridge.SplitCaseFixedPointsTransport

universe u v w x

variable {S : Type u} [CommRing S] {A : Type v} [CommRing A] {B : Type w} [CommRing B]
  {G : Type x} [Group G]
  [Algebra S A] [Algebra S B]
  [MulSemiringAction G A] [SMulCommClass G S A]
  [MulSemiringAction G B] [SMulCommClass G S B]

/-- A `G`-equivariant `S`-algebra equivalence restricts to the fixed points. -/
noncomputable def fixedPointsAlgEquivOfEquiv (e : A ≃ₐ[S] B)
    (he : ∀ (g : G) (a : A), e (g • a) = g • e a) :
    FixedPoints.subalgebra S A G ≃ₐ[S] FixedPoints.subalgebra S B G where
  toFun f := ⟨e f, by
    intro g
    rw [← he g f, f.2 g]⟩
  invFun f := ⟨e.symm f, by
    intro g
    apply e.injective
    rw [he g (e.symm f), e.apply_symm_apply, f.2 g]⟩
  left_inv f := by ext; exact e.symm_apply_apply _
  right_inv f := by ext; exact e.apply_symm_apply _
  map_add' f h := by ext; exact map_add e _ _
  map_mul' f h := by ext; exact map_mul e _ _
  commutes' s := by ext; exact e.commutes s

end ABCBridge.SplitCaseFixedPointsTransport