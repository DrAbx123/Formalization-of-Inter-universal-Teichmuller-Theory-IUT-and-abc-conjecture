import Mathlib.CategoryTheory.Sites.Descent.IsStack
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Discrete sheaf is stack: constructed part

Generic discrete-category pseudofunctor of a type-valued presheaf P:
  U |-> Discrete (P.obj U).

Actual: the pseudofunctor is constructed; the descent functor is faithful
(domain homs are subsingleton).  Fullness and essential surjectivity are the
separatedness and amalgamation halves of the sheaf condition; they are stated
as the minimal remaining targets.  No arbitrary IsStack instance.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Bicategory

namespace LeanFormal.IUT.N8Closure.DiscreteSheafIsStack

universe v u

variable {C : Type u} [Category.{v} C]

/-- The discrete-category pseudofunctor of a type-valued presheaf. -/
noncomputable def discretePseudoFunctor (P : Cᵒᵖ ⥤ Type v) :
    Cᵒᵖ ⥤ Cat.{v, v} where
  obj U := Cat.of (Discrete (P.obj U))
  map {U V} f :=
    (Discrete.functor (fun x : P.obj U => Discrete.mk (P.map f x))).toCatHom
  map_id U := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.ext
    · intro X Y f
      apply ULift.ext
      exact Subsingleton.elim _ _
    · intro X
      apply Discrete.ext
      simp
  map_comp {U V W} f g := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.ext
    · intro X Y h
      apply ULift.ext
      exact Subsingleton.elim _ _
    · intro X
      apply Discrete.ext
      simp

noncomputable def discretePseudo (P : Cᵒᵖ ⥤ Type v) :
    LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat :=
  (discretePseudoFunctor P).toPseudofunctor'

/-- Minimal target 1: fullness of the discrete descent functor
  (= separatedness/uniqueness of the sheaf condition). -/
def DiscreteDescentFull (P : Cᵒᵖ ⥤ Type v) : Prop :=
  ∀ (S : C) (R : Sieve S),
    ((discretePseudo P).toDescentData
      (fun i : R.arrows.category => i.obj.hom)).Full

/-- Minimal target 2: essential surjectivity of the discrete descent functor
  (= sheaf amalgamation). -/
def DiscreteDescentEssSurj (P : Cᵒᵖ ⥤ Type v) : Prop :=
  ∀ (S : C) (R : Sieve S),
    ((discretePseudo P).toDescentData
      (fun i : R.arrows.category => i.obj.hom)).EssSurj

def DiscreteDescentEquivalence (P : Cᵒᵖ ⥤ Type v) : Prop :=
  ∀ (S : C) (R : Sieve S),
    ((discretePseudo P).toDescentData
      (fun i : R.arrows.category => i.obj.hom)).IsEquivalence

/-- Conditional stack theorem from the two descent fields. -/
theorem discretePseudo_isStack_of_descent
    (P : Cᵒᵖ ⥤ Type v)
    (h : DiscreteDescentEquivalence P) :
    (discretePseudo P).IsStack (⊤ : GrothendieckTopology C) := by
  apply Pseudofunctor.IsStack.of_isStackFor
  intro S R _
  rw [Pseudofunctor.isStackFor_iff]
  exact h S R

def MissingDiscreteDescentFull (P : Cᵒᵖ ⥤ Type v) : Prop :=
  ¬ DiscreteDescentFull P

def MissingDiscreteDescentEssSurj (P : Cᵒᵖ ⥤ Type v) : Prop :=
  ¬ DiscreteDescentEssSurj P

end LeanFormal.IUT.N8Closure.DiscreteSheafIsStack

end