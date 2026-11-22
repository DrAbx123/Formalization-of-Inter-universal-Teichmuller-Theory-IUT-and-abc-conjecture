/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Place/label base-category family of the finite-stage model

A structure packaging the base categories of the place/label model family.
This is the self-contained base-category part of IUTchI, Definition 6.13,
(i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

/-- A place/label family of base categories. -/
structure StageLabeledBaseCategoryFamily (Label : Type u) where
  base : (NumberField.FinitePlace K × Label) -> CategoryTheory.Cat.{u, u}

namespace StageLabeledBaseCategoryFamily

/-- The family associated to the finite-stage model Frobenioids. -/
noncomputable def ofStageModel (Label : Type u) :
    StageLabeledBaseCategoryFamily (K := K) Label where
  base := fun index =>
    (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
      |>.baseCategory

@[simp] theorem ofStageModel_apply
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    (ofStageModel (K := K) Label).base index =
      (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
        |>.baseCategory :=
  rfl

end StageLabeledBaseCategoryFamily

#check StageLabeledBaseCategoryFamily
#check StageLabeledBaseCategoryFamily.ofStageModel

end SourceFrobenioidSystem
end Iut
