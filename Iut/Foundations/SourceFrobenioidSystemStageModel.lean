/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystem
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Stage-model instances of the minimal Frobenioid system

This file instantiates the minimal family of `SourceFrobenioidSystem` with
the concrete finite-place model Frobenioids of
`SourceFiniteStageModelFrobenioid`.

An additional label type is allowed, so the index is `place × label`.  This
is the formal counterpart of the place/label indexing of the system of
Frobenioids in IUTchI, Definition 6.13, (i).  No gluing or poly-action is
asserted here.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

/-- Finite-place model Frobenioids, indexed by place and an arbitrary label type. -/
noncomputable def stageModelLabeledFrobenioidSystem
    (Label : Type u) [Nonempty Label] :
    FrobenioidSystem (NumberField.FinitePlace K × Label) where
  presentation := fun index =>
    SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1

/-- The associated base-category family. -/
noncomputable def stageModelLabeledBaseCategoryFamily
    (Label : Type u) [Nonempty Label] :
    (NumberField.FinitePlace K × Label) -> CategoryTheory.Cat.{u, u} :=
  fun index =>
    (stageModelLabeledFrobenioidSystem (K := K) Label).baseCategory index

#check stageModelLabeledFrobenioidSystem
#check stageModelLabeledBaseCategoryFamily

end SourceFrobenioidSystem
end Iut
