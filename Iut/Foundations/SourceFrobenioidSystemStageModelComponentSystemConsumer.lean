/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelPresentationComponentFieldsConsumer
import Iut.Foundations.SourceFrobenioidSystem

/-!
# Consumer: system assembled from presentation components

Builds the actual system of Frobenioids from the component presentation family.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

noncomputable def stageModelComponentSystemConsumer
    (Label : Type u) :
    FrobenioidSystem (NumberField.FinitePlace K × Label) where
  presentation := stageModelComponentPresentationFamily (K := K) Label

@[simp] theorem stageModelComponentSystemConsumer_presentation
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    (stageModelComponentSystemConsumer (K := K) Label).presentation index =
      stageModelComponentPresentationFamily (K := K) Label index :=
  rfl

@[simp] theorem stageModelComponentSystemConsumer_baseCategory
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    (stageModelComponentSystemConsumer (K := K) Label).baseCategory index =
      stageModelComponentBaseFamily (K := K) Label index :=
  rfl

noncomputable def stageModelComponentSystemConsumer_axioms
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    ((stageModelComponentSystemConsumer (K := K) Label).presentation index)
      |>.preFrobenioid.FrobenioidAxioms :=
  (stageModelPresentationComponentFamily (K := K) Label index).axioms

end SourceFrobenioidSystem
end Iut
