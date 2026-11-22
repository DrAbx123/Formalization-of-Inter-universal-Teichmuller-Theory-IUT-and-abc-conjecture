/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelAxioms

/-!
# Consumer: dependent axiom family of the stage-model system

Packages the component Definition 1.3 axiom packages of the place/label
stage-model system as a dependent family.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable (Label : Type u) [Nonempty Label]

/-- Dependent family of component axioms. -/
noncomputable def stageModelAxiomsFamilyConsumer :
    (index : NumberField.FinitePlace K × Label) ->
      ((stageModelLabeledFrobenioidSystem (K := K) Label).presentation index)
        |>.preFrobenioid.FrobenioidAxioms :=
  fun index => stageModelLabeledFrobenioidSystem_axioms (K := K) Label index

@[simp] theorem stageModelAxiomsFamilyConsumer_apply
    (index : NumberField.FinitePlace K × Label) :
    stageModelAxiomsFamilyConsumer (K := K) Label index =
      stageModelLabeledFrobenioidSystem_axioms (K := K) Label index :=
  rfl

#check stageModelAxiomsFamilyConsumer
#check stageModelAxiomsFamilyConsumer_apply

end SourceFrobenioidSystem
end Iut
