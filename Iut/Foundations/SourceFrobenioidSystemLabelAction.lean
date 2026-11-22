/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystem

/-!
# Label action data for a system of Frobenioids

A labeling of the index type together with a group action on the label type.
This records the data-level label action used in IUTchI, Definition 6.13,
(i); componentwise comparison is left to the gluing units.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota : Type u}

/-- Labels on the components, plus an action on the label type. -/
structure LabelAction (iota : Type u) (Label : Type u) (G : Type u) [Group G] where
  label : iota -> Label
  action : G →* Equiv.Perm Label

namespace LabelAction

variable {Label : Type u} {G : Type u} [Group G]

def apply (data : LabelAction iota Label G) (g : G) (index : iota) : Label :=
  data.action g (data.label index)

@[simp] theorem apply_one
    (data : LabelAction iota Label G) (index : iota) :
    data.apply 1 index = data.label index := by
  change data.action 1 (data.label index) = data.label index
  rw [map_one]
  rfl

end LabelAction

end FrobenioidSystem

#check FrobenioidSystem.LabelAction
#check FrobenioidSystem.LabelAction.apply

end Iut
