/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelPolyActionConsumer

/-!
# Consumer: label-action hom of the stage-model system

Exposes the actual label-action monoid homomorphism of the place/label
stage-model system and its triviality.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable (Label : Type u) [Nonempty Label]

/-- The label-action monoid homomorphism. -/
noncomputable def stageModelLabelActionConsumer (G : Type u) [Group G] :
    G →* Equiv.Perm (NumberField.FinitePlace K × Label) :=
  (stageModelPolyActionConsumer (K := K) Label G).labelAction

@[simp] theorem stageModelLabelActionConsumer_eq_one
    (G : Type u) [Group G] :
    stageModelLabelActionConsumer (K := K) Label G =
      (1 : G →* Equiv.Perm (NumberField.FinitePlace K × Label)) :=
  rfl

@[simp] theorem stageModelLabelActionConsumer_apply
    (G : Type u) [Group G] (g : G)
    (index : NumberField.FinitePlace K × Label) :
    stageModelLabelActionConsumer (K := K) Label G g index = index :=
  rfl

#check stageModelLabelActionConsumer
#check stageModelLabelActionConsumer_eq_one

end SourceFrobenioidSystem
end Iut
