/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairBaseConsumer

/-!
# Consumer: base-category family of the two-component system

The Bool-indexed dependent family of base categories and its connectedness.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

noncomputable def pairBaseFamily
    (left right : FrobenioidPresentation.{0}) :
    (index : Bool) -> CategoryTheory.Cat.{0, 0} :=
  fun index => pairBaseCategoryConsumer left right index

@[simp] theorem pairBaseFamily_apply
    (left right : FrobenioidPresentation.{0}) (index : Bool) :
    pairBaseFamily left right index =
      pairBaseCategoryConsumer left right index :=
  rfl

theorem pairBaseFamily_isConnected
    (left right : FrobenioidPresentation.{0}) (index : Bool) :
    CategoryTheory.IsConnected (pairBaseFamily left right index) := by
  rw [pairBaseFamily_apply]
  exact pairBaseCategoryConsumer_isConnected left right index

end FrobenioidSystem

#check FrobenioidSystem.pairBaseFamily
#check FrobenioidSystem.pairBaseFamily_isConnected

end Iut
