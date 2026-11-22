/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModel
import Iut.Foundations.SourceFrobenioidSystemBaseCategory

/-!
# Consumer: base categories of the stage-model system

Consumes the place/label stage-model system and its base-category API,
exposing the actual base category of each component and its connectedness.
This is Gluing-independent and serves IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable (Label : Type u) [Nonempty Label]

/-- Base category of a place/label stage-model component. -/
noncomputable def stageModelBaseCategoryConsumer
    (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.Cat.{u, u} :=
  (stageModelLabeledFrobenioidSystem (K := K) Label).baseCategory index

@[simp] theorem stageModelBaseCategoryConsumer_eq
    (index : NumberField.FinitePlace K × Label) :
    stageModelBaseCategoryConsumer (K := K) Label index =
      (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
        |>.baseCategory :=
  rfl

theorem stageModelBaseCategoryConsumer_isConnected
    (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.IsConnected
      (stageModelBaseCategoryConsumer (K := K) Label index) :=
  (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
    |>.baseConnected

#check stageModelBaseCategoryConsumer
#check stageModelBaseCategoryConsumer_eq
#check stageModelBaseCategoryConsumer_isConnected

end SourceFrobenioidSystem
end Iut
