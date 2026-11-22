/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Label-action laws on place/label indices

A label permutation acts on the place/label index of the finite-stage model
family.  This file records the action's one/mul laws, the data-level
counterpart of the label poly-action of IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u} {G : Type u} [Group G]

/-- The label action on place/label indices. -/
def stageModelLabelAction (action : G →* Equiv.Perm Label)
    (g : G) (index : NumberField.FinitePlace K × Label) :
    NumberField.FinitePlace K × Label :=
  (index.1, action g index.2)

@[simp] theorem stageModelLabelAction_one (action : G →* Equiv.Perm Label)
    (index : NumberField.FinitePlace K × Label) :
    stageModelLabelAction (K := K) action 1 index = index := by
  rcases index with ⟨place, label⟩
  change (place, action 1 label) = (place, label)
  rw [map_one]
  rfl

@[simp] theorem stageModelLabelAction_mul (action : G →* Equiv.Perm Label)
    (g h : G) (index : NumberField.FinitePlace K × Label) :
    stageModelLabelAction (K := K) action (g * h) index =
      stageModelLabelAction (K := K) action g
        (stageModelLabelAction (K := K) action h index) := by
  rcases index with ⟨place, label⟩
  change (place, action (g * h) label) = (place, action g (action h label))
  rw [map_mul]
  rfl

#check stageModelLabelAction
#check stageModelLabelAction_one
#check stageModelLabelAction_mul

end SourceFrobenioidSystem
end Iut
