/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelPresentationFamilyConsumer

/-!
# Consumer: dependent axiom family of the presentation family

Packages the Definition 1.3 axiom packages of the place/label presentation
family as a dependent family.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

noncomputable def stageModelPresentationAxiomsFamilyConsumer
    (Label : Type u) :
    (index : NumberField.FinitePlace K × Label) ->
      (stageModelPresentationFamilyConsumer (K := K) Label index)
        |>.preFrobenioid.FrobenioidAxioms :=
  fun index =>
    stageModelPresentationAxiomsConsumer (K := K) Label index

@[simp] theorem stageModelPresentationAxiomsFamilyConsumer_apply
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    stageModelPresentationAxiomsFamilyConsumer (K := K) Label index =
      stageModelPresentationAxiomsConsumer (K := K) Label index :=
  rfl

end SourceFrobenioidSystem
end Iut
