/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystem

/-!
# Base categories of a system of Frobenioids

The D-Theta+-ellNF-Hodge theater associated to a system of Frobenioids is
its system of base categories (IUTchI, Theorem A / Definition 6.13, (i)).
This file packages the base-category family extracted from a
`FrobenioidSystem` and records connectedness of each component.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota : Type u}

/-- The base-category family of a system of Frobenioids. -/
def baseCategoryFamily (system : FrobenioidSystem iota) :
    iota -> CategoryTheory.Cat.{u, u} :=
  fun index => system.baseCategory index

@[simp] theorem baseCategoryFamily_apply
    (system : FrobenioidSystem iota) (index : iota) :
    system.baseCategoryFamily index = system.baseCategory index :=
  rfl

theorem baseCategoryFamily_isConnected
    (system : FrobenioidSystem iota) (index : iota) :
    CategoryTheory.IsConnected (system.baseCategoryFamily index) :=
  system.baseCategory_isConnected index

end FrobenioidSystem

#check FrobenioidSystem.baseCategoryFamily
#check FrobenioidSystem.baseCategoryFamily_isConnected

end Iut
