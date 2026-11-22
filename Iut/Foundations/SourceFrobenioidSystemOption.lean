/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystem

/-!
# Adding one component to a system of Frobenioids

`Option iota` extends an index type by one point.  This is the minimal
operation for adjoining one more Frobenioid presentation to a system
(e.g. an additional label or place component).
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota : Type u}

/-- Add one new component to a system. -/
def option (system : FrobenioidSystem iota)
    (presentation : FrobenioidPresentation.{u}) :
    FrobenioidSystem (Option iota) where
  presentation := fun index =>
    match index with
    | none => presentation
    | some i => system.presentation i

@[simp] theorem option_none
    (system : FrobenioidSystem iota)
    (presentation : FrobenioidPresentation.{u}) :
    (option system presentation).presentation none = presentation :=
  rfl

@[simp] theorem option_some
    (system : FrobenioidSystem iota)
    (presentation : FrobenioidPresentation.{u}) (index : iota) :
    (option system presentation).presentation (some index) =
      system.presentation index :=
  rfl

end FrobenioidSystem

#check FrobenioidSystem.option
#check FrobenioidSystem.option_none
#check FrobenioidSystem.option_some

end Iut
