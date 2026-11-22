/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystem

/-!
# Base categories of a system of Frobenioids

The family of base categories extracted from a system of Frobenioids; this
is the actual data of the D-Theta+-ellNF system of base categories
(IUTchI, Theorem A / Definition 6.13, (i)).
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota : Type u}

/-- The base-category family. -/
def baseCategories (system : FrobenioidSystem iota) :
    iota -> CategoryTheory.Cat.{u, u} :=
  fun index => system.baseCategory index

@[simp] theorem baseCategories_apply
    (system : FrobenioidSystem iota) (index : iota) :
    system.baseCategories index = system.baseCategory index :=
  rfl

theorem baseCategories_isConnected
    (system : FrobenioidSystem iota) (index : iota) :
    CategoryTheory.IsConnected (system.baseCategories index) :=
  system.baseCategory_isConnected index

end FrobenioidSystem

#check FrobenioidSystem.baseCategories
#check FrobenioidSystem.baseCategories_isConnected

end Iut
