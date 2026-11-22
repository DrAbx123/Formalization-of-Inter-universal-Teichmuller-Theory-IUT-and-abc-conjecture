import Mathlib.RingTheory.Invariant.Basic
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

/-!
# Componentwise fixed points of a finite product

For a finite family of `S`-algebras `T k` with componentwise `G`-actions, the
fixed points of the product algebra are the product of the fixed-point
subalgebras.  This is the product step needed by the global atom assembly.
-/
namespace ABCBridge.SplitCasePiFixedPoints

universe u v w

variable {S : Type u} [CommRing S] {G : Type v} [Group G]
  {κ : Type w} [Fintype κ] (T : κ → Type u)
  [∀ k, CommRing (T k)] [∀ k, Algebra S (T k)]
  [∀ k, MulSemiringAction G (T k)] [∀ k, SMulCommClass G S (T k)]

/-- Componentwise `G`-action on the product algebra. -/
@[implicit_reducible] noncomputable def piMulSemiringAction : MulSemiringAction G (∀ k, T k) where
  smul g f := fun k => g • f k
  one_smul f := by funext k; simp
  mul_smul g h f := by funext k; simp [mul_smul]
  smul_zero g := by funext k; simp
  smul_add g f h := by funext k; simp
  smul_one g := by funext k; simp
  smul_mul g f h := by funext k; simp

@[implicit_reducible] noncomputable def piSMulCommClass :
    letI : MulSemiringAction G (∀ k, T k) := piMulSemiringAction (T := T)
    SMulCommClass G S (∀ k, T k) := by
  letI : MulSemiringAction G (∀ k, T k) := piMulSemiringAction (T := T)
  exact ⟨fun g s f => by funext k; simp [smul_comm]⟩

/-- Fixed points of a finite product are the product of the fixed points. -/
noncomputable def fixedPointsPiAlgEquiv :
    letI : MulSemiringAction G (∀ k, T k) := piMulSemiringAction (T := T)
    letI : SMulCommClass G S (∀ k, T k) := piSMulCommClass (T := T)
    FixedPoints.subalgebra S (∀ k, T k) G ≃ₐ[S]
      ∀ k, FixedPoints.subalgebra S (T k) G := by
  letI : MulSemiringAction G (∀ k, T k) := piMulSemiringAction (T := T)
  letI : SMulCommClass G S (∀ k, T k) := piSMulCommClass (T := T)
  refine
    { toFun := fun f k =>
        ⟨f.val k, fun g => congrFun (f.2 g) k⟩
      invFun := fun f =>
        ⟨fun k => f k, fun g => funext fun k => (f k).2 g⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_mul' := ?_
      commutes' := ?_ }
  · intro f
    ext k <;> rfl
  · intro f
    ext k <;> rfl
  · intro f h
    ext k <;> rfl
  · intro f h
    ext k <;> rfl
  · intro s
    ext k <;> rfl

end ABCBridge.SplitCasePiFixedPoints