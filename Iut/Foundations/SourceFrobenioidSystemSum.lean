/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystem

/-!
# Sum of systems of Frobenioids

The disjoint union of two systems: a family indexed by `iota ⊕ kappa`.
This gives the formal operation of combining place and label components
into one system of Frobenioids (IUTchI, Definition 6.13, (i)).
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota kappa : Type u}

/-- Disjoint union of two systems. -/
def sum (left : FrobenioidSystem iota) (right : FrobenioidSystem kappa) :
    FrobenioidSystem (iota ⊕ kappa) where
  presentation := Sum.elim left.presentation right.presentation

@[simp] theorem sum_inl
    (left : FrobenioidSystem iota) (right : FrobenioidSystem kappa) (index : iota) :
    (sum left right).presentation (Sum.inl index) = left.presentation index :=
  rfl

@[simp] theorem sum_inr
    (left : FrobenioidSystem iota) (right : FrobenioidSystem kappa) (index : kappa) :
    (sum left right).presentation (Sum.inr index) = right.presentation index :=
  rfl

end FrobenioidSystem

#check FrobenioidSystem.sum
#check FrobenioidSystem.sum_inl
#check FrobenioidSystem.sum_inr

end Iut
