/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingLabelConsumer

/-!
# Consumer: label-action one/mul laws on place/label indices

The label action of the place/label system satisfies the group-action laws.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u} {G : Type u} [Group G]

namespace StageModelSystemDataGluing

variable (data : StageModelSystemDataGluing (K := K) Label G)

@[simp] theorem applyLabel_one
    (index : NumberField.FinitePlace K × Label) :
    data.applyLabel 1 index = index := by
  rcases index with ⟨place, label⟩
  change (place, data.labelAction.action 1 label) = (place, label)
  rw [map_one]
  rfl

@[simp] theorem applyLabel_mul
    (g h : G) (index : NumberField.FinitePlace K × Label) :
    data.applyLabel (g * h) index =
      data.applyLabel g (data.applyLabel h index) := by
  rcases index with ⟨place, label⟩
  change (place, data.labelAction.action (g * h) label) =
    (place, data.labelAction.action g (data.labelAction.action h label))
  rw [map_mul]
  rfl

end StageModelSystemDataGluing

#check StageModelSystemDataGluing.applyLabel_one
#check StageModelSystemDataGluing.applyLabel_mul

end SourceFrobenioidSystem
end Iut
