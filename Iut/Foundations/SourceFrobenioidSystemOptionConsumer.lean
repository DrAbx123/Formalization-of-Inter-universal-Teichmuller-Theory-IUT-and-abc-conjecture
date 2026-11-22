/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemOption

/-!
# Consumer: adjoining one component to a system

Projects the old components and the newly adjoined component of an `Option`
extension of a system of Frobenioids.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota : Type u}

/-- The presentation at an `Option` index. -/
noncomputable def optionPresentation
    (system : FrobenioidSystem iota)
    (presentation : FrobenioidPresentation.{u}) (index : Option iota) :
    FrobenioidPresentation.{u} :=
  (option system presentation).presentation index

@[simp] theorem optionPresentation_none
    (system : FrobenioidSystem iota)
    (presentation : FrobenioidPresentation.{u}) :
    optionPresentation system presentation none = presentation :=
  rfl

@[simp] theorem optionPresentation_some
    (system : FrobenioidSystem iota)
    (presentation : FrobenioidPresentation.{u}) (index : iota) :
    optionPresentation system presentation (some index) =
      system.presentation index :=
  rfl

end FrobenioidSystem

#check FrobenioidSystem.optionPresentation
#check FrobenioidSystem.optionPresentation_none
#check FrobenioidSystem.optionPresentation_some

end Iut
