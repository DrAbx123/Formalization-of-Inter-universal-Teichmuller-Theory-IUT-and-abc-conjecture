/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemSumConsumer

/-!
# Consumer: base categories of the disjoint-union system

The base category at a sum index is the base category of the corresponding
summand; hence every component is connected.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota kappa : Type u}

noncomputable def sumBaseCategoryConsumer
    (left : FrobenioidSystem iota) (right : FrobenioidSystem kappa)
    (index : iota ⊕ kappa) : CategoryTheory.Cat.{u, u} :=
  (left.sum right).baseCategory index

@[simp] theorem sumBaseCategoryConsumer_inl
    (left : FrobenioidSystem iota) (right : FrobenioidSystem kappa)
    (index : iota) :
    sumBaseCategoryConsumer left right (Sum.inl index) =
      left.baseCategory index :=
  rfl

@[simp] theorem sumBaseCategoryConsumer_inr
    (left : FrobenioidSystem iota) (right : FrobenioidSystem kappa)
    (index : kappa) :
    sumBaseCategoryConsumer left right (Sum.inr index) =
      right.baseCategory index :=
  rfl

theorem sumBaseCategoryConsumer_isConnected
    (left : FrobenioidSystem iota) (right : FrobenioidSystem kappa)
    (index : iota ⊕ kappa) :
    CategoryTheory.IsConnected (sumBaseCategoryConsumer left right index) :=
  (left.sum right).baseCategory_isConnected index

end FrobenioidSystem

#check FrobenioidSystem.sumBaseCategoryConsumer
#check FrobenioidSystem.sumBaseCategoryConsumer_inl
#check FrobenioidSystem.sumBaseCategoryConsumer_inr
#check FrobenioidSystem.sumBaseCategoryConsumer_isConnected

end Iut
