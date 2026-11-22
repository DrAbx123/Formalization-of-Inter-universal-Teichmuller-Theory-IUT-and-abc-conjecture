/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemOptionConsumer

/-!
# Consumer: base categories of an Option-extended system

The base category at `none` is the new presentation's base category; at
`some i` it is the old component's base category.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota : Type u}

noncomputable def optionBaseCategoryConsumer
    (system : FrobenioidSystem iota)
    (presentation : FrobenioidPresentation.{u}) (index : Option iota) :
    CategoryTheory.Cat.{u, u} :=
  (option system presentation).baseCategory index

@[simp] theorem optionBaseCategoryConsumer_none
    (system : FrobenioidSystem iota)
    (presentation : FrobenioidPresentation.{u}) :
    optionBaseCategoryConsumer system presentation none =
      presentation.baseCategory :=
  rfl

@[simp] theorem optionBaseCategoryConsumer_some
    (system : FrobenioidSystem iota)
    (presentation : FrobenioidPresentation.{u}) (index : iota) :
    optionBaseCategoryConsumer system presentation (some index) =
      system.baseCategory index :=
  rfl

theorem optionBaseCategoryConsumer_isConnected
    (system : FrobenioidSystem iota)
    (presentation : FrobenioidPresentation.{u}) (index : Option iota) :
    CategoryTheory.IsConnected
      (optionBaseCategoryConsumer system presentation index) := by
  cases index with
  | none => exact presentation.baseConnected
  | some index => exact system.baseCategory_isConnected index
end FrobenioidSystem


#check FrobenioidSystem.optionBaseCategoryConsumer
#check FrobenioidSystem.optionBaseCategoryConsumer_none
#check FrobenioidSystem.optionBaseCategoryConsumer_some

end Iut
