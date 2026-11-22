/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Frobenioid axioms of the place/label base-category family

Each component of the place/label model family is a genuine Frobenioid
presentation with the full Definition 1.3 axiom package.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

noncomputable def stageModelBaseCategoryFamilyStructure_axioms
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
      |>.preFrobenioid.FrobenioidAxioms :=
  (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1).axioms

#check stageModelBaseCategoryFamilyStructure_axioms

end SourceFrobenioidSystem
end Iut
