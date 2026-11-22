/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModel
import Iut.Foundations.SourceFrobenioidSystemPolyAction

/-!
# Consumer: trivial label action on the stage-model system

Consumes the place/label stage-model system and its label poly-action data.
This is a Gluing-independent consumer serving IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable (Label : Type u) [Nonempty Label]

/-- Trivial label action on the place/label stage-model system. -/
noncomputable def stageModelPolyActionConsumer
    (G : Type u) [Group G] :
    FrobenioidSystemPolyAction
      (stageModelLabeledFrobenioidSystem (K := K) Label) G :=
  FrobenioidSystemPolyAction.trivial _ G

@[simp] theorem stageModelPolyActionConsumer_labelAction
    (G : Type u) [Group G] :
    (stageModelPolyActionConsumer (K := K) Label G).labelAction =
      (1 : G →* Equiv.Perm (NumberField.FinitePlace K × Label)) :=
  rfl

#check stageModelPolyActionConsumer
#check stageModelPolyActionConsumer_labelAction

end SourceFrobenioidSystem
end Iut
