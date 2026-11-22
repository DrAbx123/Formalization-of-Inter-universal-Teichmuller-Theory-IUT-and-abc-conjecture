/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Place/label model family structure

A structure bundling the presentation family and base-category family of the
finite-stage model.  This is the self-contained system-of-Frobenioids data
of IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

/-- Bundled place/label family of model Frobenioids and base categories. -/
structure StageModelFamily (Label : Type u) where
  presentation :
    (NumberField.FinitePlace K × Label) -> FrobenioidPresentation.{u}
  base :
    (NumberField.FinitePlace K × Label) -> CategoryTheory.Cat.{u, u}
  base_eq :
    forall index, base index = (presentation index).baseCategory

namespace StageModelFamily

/-- The concrete finite-stage model family. -/
noncomputable def ofFiniteStage (Label : Type u) :
    StageModelFamily (K := K) Label where
  presentation := fun index =>
    SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1
  base := fun index =>
    (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
      |>.baseCategory
  base_eq := fun index => rfl

@[simp] theorem ofFiniteStage_presentation
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    (ofFiniteStage (K := K) Label).presentation index =
      SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1 :=
  rfl

end StageModelFamily

#check StageModelFamily
#check StageModelFamily.ofFiniteStage

end SourceFrobenioidSystem
end Iut
