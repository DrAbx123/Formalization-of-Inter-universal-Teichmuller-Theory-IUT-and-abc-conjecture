/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelComponentSystemConsumer

/-!
# Consumer: dependent axiom family of the component system

The component systems' Definition 1.3 axiom packages as a dependent family.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

noncomputable def stageModelComponentSystemAxiomsFamily
    (Label : Type u) :
    (index : NumberField.FinitePlace K × Label) ->
      ((stageModelComponentSystemConsumer (K := K) Label).presentation index)
        |>.preFrobenioid.FrobenioidAxioms :=
  fun index => (stageModelPresentationComponentFamily (K := K) Label index).axioms

@[simp] theorem stageModelComponentSystemAxiomsFamily_apply
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    stageModelComponentSystemAxiomsFamily (K := K) Label index =
      (stageModelPresentationComponentFamily (K := K) Label index).axioms :=
  rfl

end SourceFrobenioidSystem
end Iut
