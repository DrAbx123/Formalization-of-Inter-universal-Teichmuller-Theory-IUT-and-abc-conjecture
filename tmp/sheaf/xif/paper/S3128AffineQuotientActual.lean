import Mathlib.Algebra.Ring.Action.Invariant
import Mathlib.Algebra.Algebra.Basic

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- The fixed subring of a ring with an action of a monoid. -/
def S3128FixedSubring (G : Type) (A : Type) [Monoid G] [Ring A]
    [MulSemiringAction G A] : Subring A where
  carrier := {a | forall g : G, g • a = a}
  mul_mem' := by
    intro a b ha hb g
    rw [smul_mul', ha g, hb g]
  one_mem' := by
    intro g
    rw [smul_one]
  add_mem' := by
    intro a b ha hb g
    rw [smul_add, ha g, hb g]
  zero_mem' := by
    intro g
    rw [smul_zero]
  neg_mem' := by
    intro a ha g
    rw [smul_neg, ha g]

/-- The universal property of the affine quotient by a group action:
any invariant ring map factors uniquely through the fixed subring. -/
theorem S3128FixedSubring_lift (G : Type) [Monoid G]
    (A B : Type) [Ring A] [MulSemiringAction G A] [Ring B]
    (f : B →+* A) (hf : forall (b : B) (g : G), g • f b = f b) :
    ∃! (fbar : B →+* S3128FixedSubring G A),
      (S3128FixedSubring G A).subtype.comp fbar = f := by
  refine ⟨RingHom.codRestrict f (S3128FixedSubring G A)
    (fun b => ?_), ?_, ?_⟩
  · intro g
    exact hf b g
  · ext b
    rfl
  · intro fbar h
    ext b
    have hb := congrArg (fun q : B →+* A => q b) h
    exact hb

/-- The affine quotient target: the fixed subring satisfies the universal
property of the quotient of an affine scheme by a finite group action. -/
def S3128AffineQuotientTarget (G : Type) [Monoid G]
    (A : Type) [Ring A] [MulSemiringAction G A] : Prop :=
  forall (B : Type) [Ring B] (f : B →+* A),
    (forall (b : B) (g : G), g • f b = f b) ->
      ∃! (fbar : B →+* S3128FixedSubring G A),
        (S3128FixedSubring G A).subtype.comp fbar = f

/-- The affine quotient target holds. -/
theorem S3128AffineQuotientTarget_holds (G : Type) [Monoid G]
    (A : Type) [Ring A] [MulSemiringAction G A] :
    S3128AffineQuotientTarget G A :=
  fun B _ f hf => S3128FixedSubring_lift G A B f hf

#check S3128FixedSubring
#check S3128FixedSubring_lift
#check S3128AffineQuotientTarget
#check S3128AffineQuotientTarget_holds

end LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual
end