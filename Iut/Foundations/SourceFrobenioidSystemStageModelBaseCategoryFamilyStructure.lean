/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Place/label base-category family structure

A structure bundling the base-category family of the finite-stage model
family, as the D-Theta+-ellNF system of base categories of IUTchI,
Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

/-- A place/label base-category family. -/
structure StageModelBaseCategoryFamily (Label : Type u) where
  base : (NumberField.FinitePlace K × Label) -> CategoryTheory.Cat.{u, u}
  base_eq :
    forall index,
      base index =
        (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
          |>.baseCategory

namespace StageModelBaseCategoryFamily

/-- The concrete finite-stage base-category family. -/
noncomputable def ofFiniteStage (Label : Type u) :
    StageModelBaseCategoryFamily (K := K) Label where
  base := fun index =>
    (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
      |>.baseCategory
  base_eq := fun index => rfl

@[simp] theorem ofFiniteStage_base
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    (ofFiniteStage (K := K) Label).base index =
      (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
        |>.baseCategory :=
  rfl

end StageModelBaseCategoryFamily

#check StageModelBaseCategoryFamily
#check StageModelBaseCategoryFamily.ofFiniteStage

end SourceFrobenioidSystem
end Iut
