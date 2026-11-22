/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemConstant

/-!
# Consumer: constant system of Frobenioids

Projects the constant family of Frobenioid presentations and its base
categories.  Gluing-independent consumer of IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota : Type u}

/-- The presentation at any index of a constant system. -/
noncomputable def constantPresentation
    (presentation : FrobenioidPresentation.{u}) (iota : Type u) (index : iota) :
    FrobenioidPresentation.{u} :=
  (constant presentation iota).presentation index

@[simp] theorem constantPresentation_eq
    (presentation : FrobenioidPresentation.{u}) (iota : Type u) (index : iota) :
    constantPresentation presentation iota index = presentation :=
  rfl

end FrobenioidSystem

#check FrobenioidSystem.constantPresentation
#check FrobenioidSystem.constantPresentation_eq

end Iut
