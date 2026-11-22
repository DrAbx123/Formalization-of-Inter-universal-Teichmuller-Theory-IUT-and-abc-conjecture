/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Axiom family of the place/label model family

The dependent family of Definition 1.3 axiom packages over place/label
indices.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

/-- Dependent family of Frobenioid axioms over place/label indices. -/
noncomputable def stageLabeledAxiomsFamily (Label : Type u) :
    (index : NumberField.FinitePlace K × Label) ->
      (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
        |>.preFrobenioid.FrobenioidAxioms :=
  fun index =>
    (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1).axioms

@[simp] theorem stageLabeledAxiomsFamily_apply
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    stageLabeledAxiomsFamily (K := K) Label index =
      (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1).axioms :=
  rfl

#check stageLabeledAxiomsFamily
#check stageLabeledAxiomsFamily_apply

end SourceFrobenioidSystem
end Iut
