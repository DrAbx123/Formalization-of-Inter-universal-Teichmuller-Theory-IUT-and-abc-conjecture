/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Base categories of the place/label model family

The base category of each component is definitionally the base category of
the corresponding packaged model Frobenioid.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

@[simp] theorem stageModelFamilyBase_eq
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1).baseCategory =
      (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1).baseCategory :=
  rfl

#check stageModelFamilyBase_eq

end SourceFrobenioidSystem
end Iut
