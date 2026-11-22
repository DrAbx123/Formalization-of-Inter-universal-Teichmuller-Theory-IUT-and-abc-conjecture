/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelPresentationComponentFamilyConsumer

/-!
# Consumer: fields of the presentation-component family

Projects presentations, base categories, connectedness, and axioms from the
dependent family of place/label components.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

noncomputable def stageModelComponentPresentationFamily
    (Label : Type u) :
    (index : NumberField.FinitePlace K × Label) -> FrobenioidPresentation.{u} :=
  fun index => (stageModelPresentationComponentFamily (K := K) Label index).presentation

noncomputable def stageModelComponentBaseFamily
    (Label : Type u) :
    (index : NumberField.FinitePlace K × Label) -> CategoryTheory.Cat.{u, u} :=
  fun index => (stageModelPresentationComponentFamily (K := K) Label index).base

noncomputable def stageModelComponentAxiomsFamily
    (Label : Type u) :
    (index : NumberField.FinitePlace K × Label) ->
      (stageModelComponentPresentationFamily (K := K) Label index)
        |>.preFrobenioid.FrobenioidAxioms :=
  fun index => (stageModelPresentationComponentFamily (K := K) Label index).axioms

end SourceFrobenioidSystem
end Iut
