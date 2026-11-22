/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairConsumer

/-!
# Consumer: base categories of the two-component system

The two components' base categories and their connectedness.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

noncomputable def pairBaseCategoryConsumer
    (left right : FrobenioidPresentation.{0}) (index : Bool) :
    CategoryTheory.Cat.{0, 0} :=
  (pair left right).baseCategory index

@[simp] theorem pairBaseCategoryConsumer_false
    (left right : FrobenioidPresentation.{0}) :
    pairBaseCategoryConsumer left right false = left.baseCategory :=
  rfl

@[simp] theorem pairBaseCategoryConsumer_true
    (left right : FrobenioidPresentation.{0}) :
    pairBaseCategoryConsumer left right true = right.baseCategory :=
  rfl

theorem pairBaseCategoryConsumer_isConnected
    (left right : FrobenioidPresentation.{0}) (index : Bool) :
    CategoryTheory.IsConnected (pairBaseCategoryConsumer left right index) := by
  cases index with
  | false => exact left.baseConnected
  | true => exact right.baseConnected

end FrobenioidSystem

#check FrobenioidSystem.pairBaseCategoryConsumer
#check FrobenioidSystem.pairBaseCategoryConsumer_isConnected

end Iut
