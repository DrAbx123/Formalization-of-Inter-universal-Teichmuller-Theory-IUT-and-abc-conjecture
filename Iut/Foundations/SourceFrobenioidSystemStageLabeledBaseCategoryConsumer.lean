/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageLabeledBaseCategoryConnected

/-!
# Consumer: place/label base categories of the finite-stage model

Projects the concrete place/label base-category family and its connectedness.
This is the consumer-facing D-Theta+-ellNF system of base categories of
IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

/-- Base category at a place/label index. -/
noncomputable def stageLabeledBaseCategory
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.Cat.{u, u} :=
  (StageLabeledBaseCategoryFamily.ofStageModel (K := K) Label).base index

@[simp] theorem stageLabeledBaseCategory_eq
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    stageLabeledBaseCategory (K := K) Label index =
      (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
        |>.baseCategory :=
  rfl

theorem stageLabeledBaseCategory_isConnected
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.IsConnected
      (stageLabeledBaseCategory (K := K) Label index) :=
  StageLabeledBaseCategoryFamily.ofStageModel_isConnected Label index

#check stageLabeledBaseCategory
#check stageLabeledBaseCategory_eq
#check stageLabeledBaseCategory_isConnected

end SourceFrobenioidSystem
end Iut
