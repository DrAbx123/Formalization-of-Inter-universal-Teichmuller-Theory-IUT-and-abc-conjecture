/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemSum

/-!
# Consumer: disjoint union of systems

Projects the two summands of a disjoint-union system of Frobenioids.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota kappa : Type u}

/-- Presentation at a sum index. -/
noncomputable def sumPresentation
    (left : FrobenioidSystem iota) (right : FrobenioidSystem kappa)
    (index : iota ⊕ kappa) : FrobenioidPresentation.{u} :=
  (sum left right).presentation index

@[simp] theorem sumPresentation_inl
    (left : FrobenioidSystem iota) (right : FrobenioidSystem kappa)
    (index : iota) :
    sumPresentation left right (Sum.inl index) =
      left.presentation index :=
  rfl

@[simp] theorem sumPresentation_inr
    (left : FrobenioidSystem iota) (right : FrobenioidSystem kappa)
    (index : kappa) :
    sumPresentation left right (Sum.inr index) =
      right.presentation index :=
  rfl

end FrobenioidSystem

#check FrobenioidSystem.sumPresentation
#check FrobenioidSystem.sumPresentation_inl
#check FrobenioidSystem.sumPresentation_inr

end Iut
