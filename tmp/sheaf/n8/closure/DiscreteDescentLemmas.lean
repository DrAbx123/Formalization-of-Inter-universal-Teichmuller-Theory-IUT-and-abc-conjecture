import tmp.sheaf.n8.closure.DiscreteSheafIsStack
import Mathlib

/-!
# Discrete descent: minimal intermediate lemmas

The target functors for DiscreteDescentFull and DiscreteDescentEssSurj are the
discrete descent functors of the actual discrete pseudofunctor.

This file proves the unconditional intermediate facts that are independent of
the sheaf condition:

* the discrete descent functor is faithful (domain homs are subsingleton);
* Full + EssSurj give the functor IsEquivalence of the conditional stack
  theorem.

The remaining two substantive inputs are exactly DiscreteDescentFull and
DiscreteDescentEssSurj; no axiom or arbitrary instance is introduced.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Bicategory

namespace LeanFormal.IUT.N8Closure.DiscreteDescentLemmas

universe v u

variable {C : Type u} [Category.{v} C]

/-- The discrete descent functor is faithful: its domain is a discrete
category, so every hom type is a subsingleton. -/
noncomputable instance discreteDescent_faithful
    (P : Cᵒᵖ ⥤ Type v) (S : C) (R : Sieve S) :
    ((LeanFormal.IUT.N8Closure.DiscreteSheafIsStack.discretePseudo P).toDescentData
      (fun i : R.arrows.category => i.obj.hom)).Faithful where
  map_injective {X Y} := by
    intro f g h
    haveI : Subsingleton (X ⟶ Y) := ⟨fun a b => by
      rcases a with ⟨⟨ha⟩⟩
      rcases b with ⟨⟨hb⟩⟩
      congr⟩
    exact Subsingleton.elim f g

/-- Full + EssSurj assemble the descent functor into an equivalence. -/
theorem discreteDescentEquivalence_of_full_essSurj
    (P : Cᵒᵖ ⥤ Type v)
    (hfull : LeanFormal.IUT.N8Closure.DiscreteSheafIsStack.DiscreteDescentFull P)
    (hess : LeanFormal.IUT.N8Closure.DiscreteSheafIsStack.DiscreteDescentEssSurj P) :
    LeanFormal.IUT.N8Closure.DiscreteSheafIsStack.DiscreteDescentEquivalence P := by
  intro S R
  haveI : ((LeanFormal.IUT.N8Closure.DiscreteSheafIsStack.discretePseudo P).toDescentData
      (fun i : R.arrows.category => i.obj.hom)).Faithful :=
    discreteDescent_faithful P S R
  refine { faithful := inferInstance, full := hfull S R, essSurj := hess S R }

/-- Conditional stack theorem from the two exact descent targets. -/
theorem discretePseudo_isStack_of_full_essSurj
    (P : Cᵒᵖ ⥤ Type v)
    (hfull : LeanFormal.IUT.N8Closure.DiscreteSheafIsStack.DiscreteDescentFull P)
    (hess : LeanFormal.IUT.N8Closure.DiscreteSheafIsStack.DiscreteDescentEssSurj P) :
    (LeanFormal.IUT.N8Closure.DiscreteSheafIsStack.discretePseudo P).IsStack
      (⊤ : GrothendieckTopology C) :=
  LeanFormal.IUT.N8Closure.DiscreteSheafIsStack.discretePseudo_isStack_of_descent P
    (discreteDescentEquivalence_of_full_essSurj P hfull hess)

end LeanFormal.IUT.N8Closure.DiscreteDescentLemmas
