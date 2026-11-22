/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPolyAction
import Iut.Foundations.SourceFrobenioidSystemReindex

/-!
# Reindexing by a label poly-action

A label poly-action on a system of Frobenioids reindexes the system.  This
file records the resulting action on `FrobenioidSystem` itself and its
one/mul laws, the data-level counterpart of the label action in IUTchI,
Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystemPolyAction

variable {iota : Type u} {system : FrobenioidSystem iota}
variable {G : Type u} [Group G]

/-- Reindex the system by the label action of a group element. -/
def reindexSystem (action : FrobenioidSystemPolyAction system G) (g : G) :
    FrobenioidSystem iota :=
  system.reindex (action.labelAction g)

@[simp] theorem reindexSystem_one
    (action : FrobenioidSystemPolyAction system G) :
    action.reindexSystem 1 = system := by
  unfold reindexSystem
  rw [map_one]
  change system.reindex id = system
  rw [FrobenioidSystem.reindex_id]

@[simp] theorem reindexSystem_mul
    (action : FrobenioidSystemPolyAction system G) (g h : G) :
    action.reindexSystem (g * h) =
      (action.reindexSystem g).reindex (action.labelAction h) := by
  unfold reindexSystem
  rw [FrobenioidSystem.reindex_comp]
  rw [map_mul]
  congr 1

theorem reindexSystem_presentation
    (action : FrobenioidSystemPolyAction system G) (g : G) (index : iota) :
    (action.reindexSystem g).presentation index =
      system.presentation (action.labelAction g index) :=
  rfl

end FrobenioidSystemPolyAction

#check FrobenioidSystemPolyAction.reindexSystem
#check FrobenioidSystemPolyAction.reindexSystem_one
#check FrobenioidSystemPolyAction.reindexSystem_mul

end Iut
