/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPolyActionReindex
import Iut.Foundations.SourceFrobenioidSystemGluingReindex

/-!
# Poly-action on gluing data

A label action moves the whole glued system: reindex the gluing data along
the action on labels.  This is the data-level counterpart of the label
poly-action on a glued system of Frobenioids (IUTchI, Definition 6.13, (i)).
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystemPolyAction

variable {iota : Type u} {system : FrobenioidSystem iota}
variable {G : Type u} [Group G]

/-- Move gluing data by the label action of a group element. -/
def reindexGluing (action : FrobenioidSystemPolyAction system G)
    (gluing : FrobenioidSystemGluing system) (g : G) :
    FrobenioidSystemGluing (action.reindexSystem g) :=
  gluing.reindex (action.labelAction g)

@[simp] theorem reindexGluing_one
    (action : FrobenioidSystemPolyAction system G)
    (gluing : FrobenioidSystemGluing system) :
    action.reindexGluing gluing 1 = gluing :=
  rfl

end FrobenioidSystemPolyAction

#check FrobenioidSystemPolyAction.reindexGluing

end Iut
