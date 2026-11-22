/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystem

/-!
# Base-category families of systems of Frobenioids

The D-Theta+-ellNF-Hodge theater of IUTchI, Theorem A/Definition 6.13, (i),
is the system of base categories associated to a system of Frobenioids.
This file packages that base-category family as actual data and constructs it
from any `FrobenioidSystem`.
-/

open CategoryTheory

namespace Iut

universe u

/-- A family of base categories. -/
structure FrobenioidSystemBaseCategoryFamily (iota : Type u) where
  base : iota -> CategoryTheory.Cat.{u, u}

namespace FrobenioidSystemBaseCategoryFamily

variable {iota : Type u}

/-- The base-category family associated to a system of Frobenioids. -/
def ofSystem (system : FrobenioidSystem iota) :
    FrobenioidSystemBaseCategoryFamily iota where
  base := fun index => system.baseCategory index

@[simp] theorem ofSystem_apply
    (system : FrobenioidSystem iota) (index : iota) :
    (ofSystem system).base index = system.baseCategory index :=
  rfl

end FrobenioidSystemBaseCategoryFamily

#check FrobenioidSystemBaseCategoryFamily
#check FrobenioidSystemBaseCategoryFamily.ofSystem

end Iut
