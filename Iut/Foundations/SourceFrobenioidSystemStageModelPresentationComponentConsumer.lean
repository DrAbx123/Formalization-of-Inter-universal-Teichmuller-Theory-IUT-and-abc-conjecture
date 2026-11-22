/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelPresentationBaseConsumer
import Iut.Foundations.SourceFrobenioidSystemStageModelPresentationAxiomsFamilyConsumer

/-!
# Consumer: component data of the stage-model presentation family

A component bundles the actual presentation, its base category,
connectedness, and Definition 1.3 axiom package.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

structure StageModelPresentationComponent (Label : Type u)
    (index : NumberField.FinitePlace K × Label) where
  presentation : FrobenioidPresentation.{u}
  base : CategoryTheory.Cat.{u, u}
  base_eq : base = presentation.baseCategory
  connected : CategoryTheory.IsConnected base
  axioms : presentation.preFrobenioid.FrobenioidAxioms

namespace StageModelPresentationComponent

noncomputable def ofStageModel (Label : Type u)
    (index : NumberField.FinitePlace K × Label) :
    StageModelPresentationComponent (K := K) Label index where
  presentation := stageModelPresentationFamilyConsumer (K := K) Label index
  base := stageModelPresentationBaseCategoryConsumer (K := K) Label index
  base_eq := rfl
  connected := stageModelPresentationBaseCategoryConsumer_isConnected Label index
  axioms := stageModelPresentationAxiomsConsumer (K := K) Label index

end StageModelPresentationComponent

#check StageModelPresentationComponent
#check StageModelPresentationComponent.ofStageModel

end SourceFrobenioidSystem
end Iut
