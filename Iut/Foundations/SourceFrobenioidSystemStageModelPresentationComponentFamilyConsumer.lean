/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelPresentationComponentConsumer

/-!
# Consumer: family of presentation components

The dependent family of actual place/label component data.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

noncomputable def stageModelPresentationComponentFamily
    (Label : Type u) :
    (index : NumberField.FinitePlace K × Label) ->
      StageModelPresentationComponent (K := K) Label index :=
  fun index => StageModelPresentationComponent.ofStageModel (K := K) Label index

@[simp] theorem stageModelPresentationComponentFamily_apply
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    stageModelPresentationComponentFamily (K := K) Label index =
      StageModelPresentationComponent.ofStageModel (K := K) Label index :=
  rfl

end SourceFrobenioidSystem
end Iut
