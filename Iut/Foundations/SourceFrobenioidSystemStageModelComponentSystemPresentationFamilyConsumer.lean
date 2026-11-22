/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelComponentSystemConsumer

/-!
# Consumer: presentation family of the component system

Projects the presentation family of the assembled system of Frobenioids.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

noncomputable def stageModelComponentSystemPresentationFamily
    (Label : Type u) :
    (index : NumberField.FinitePlace K × Label) -> FrobenioidPresentation.{u} :=
  fun index => (stageModelComponentSystemConsumer (K := K) Label).presentation index

@[simp] theorem stageModelComponentSystemPresentationFamily_eq
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    stageModelComponentSystemPresentationFamily (K := K) Label index =
      stageModelComponentPresentationFamily (K := K) Label index :=
  rfl

end SourceFrobenioidSystem
end Iut
