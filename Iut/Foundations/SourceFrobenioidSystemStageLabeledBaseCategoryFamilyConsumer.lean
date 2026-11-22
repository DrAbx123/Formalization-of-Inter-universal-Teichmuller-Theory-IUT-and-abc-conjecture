/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageLabeledBaseCategoryFamily

/-!
# Consumer: place/label base-category family

Projects the concrete place/label base-category family, without using the
connectedness theorem.  This is a Gluing-independent downstream consumer of
IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

/-- The concrete place/label base-category family. -/
noncomputable def stageLabeledBaseCategoryFamily
    (Label : Type u) :
    (NumberField.FinitePlace K × Label) -> CategoryTheory.Cat.{u, u} :=
  fun index =>
    (StageLabeledBaseCategoryFamily.ofStageModel (K := K) Label).base index

@[simp] theorem stageLabeledBaseCategoryFamily_eq
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    stageLabeledBaseCategoryFamily (K := K) Label index =
      (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
        |>.baseCategory :=
  rfl

#check stageLabeledBaseCategoryFamily
#check stageLabeledBaseCategoryFamily_eq

end SourceFrobenioidSystem
end Iut
