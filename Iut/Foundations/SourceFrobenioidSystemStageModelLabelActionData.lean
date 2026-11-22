/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Label-action data on the place/label model family

An action of a group on the label type, transported to the place/label index
of the finite-stage model family.  This is the data-level label poly-action
of IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

/-- Label-action data on place/label indices. -/
structure StageModelLabelActionData (Label : Type u) (G : Type u) [Group G] where
  action : G →* Equiv.Perm Label

namespace StageModelLabelActionData

variable {Label : Type u} {G : Type u} [Group G]

/-- The index obtained by acting on the label component. -/
def apply (data : StageModelLabelActionData Label G)
    (g : G) (index : NumberField.FinitePlace K × Label) :
    NumberField.FinitePlace K × Label :=
  (index.1, data.action g index.2)

@[simp] theorem apply_one
    (data : StageModelLabelActionData Label G)
    (index : NumberField.FinitePlace K × Label) :
    data.apply 1 index = index := by
  rcases index with ⟨place, label⟩
  change (place, data.action 1 label) = (place, label)
  rw [map_one]
  rfl

end StageModelLabelActionData

#check StageModelLabelActionData
#check StageModelLabelActionData.apply

end SourceFrobenioidSystem
end Iut
