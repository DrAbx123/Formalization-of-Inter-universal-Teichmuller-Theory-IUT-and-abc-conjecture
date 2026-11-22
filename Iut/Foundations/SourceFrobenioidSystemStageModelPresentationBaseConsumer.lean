/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelPresentationFamilyConsumer

/-!
# Consumer: base categories of the stage-model presentation family

Projects the base category and connectedness of each place/label presentation.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

noncomputable def stageModelPresentationBaseCategoryConsumer
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.Cat.{u, u} :=
  (stageModelPresentationFamilyConsumer (K := K) Label index).baseCategory

@[simp] theorem stageModelPresentationBaseCategoryConsumer_eq
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    stageModelPresentationBaseCategoryConsumer (K := K) Label index =
      (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation
        (K := K) index.1).baseCategory :=
  rfl

theorem stageModelPresentationBaseCategoryConsumer_isConnected
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.IsConnected
      (stageModelPresentationBaseCategoryConsumer (K := K) Label index) :=
  (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation
    (K := K) index.1).baseConnected

end SourceFrobenioidSystem
end Iut
