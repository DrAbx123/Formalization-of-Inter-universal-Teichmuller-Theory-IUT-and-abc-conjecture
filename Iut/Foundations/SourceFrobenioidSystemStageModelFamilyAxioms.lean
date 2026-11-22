/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Frobenioid axioms of the place/label model family

Each place/label component of the finite-stage model family carries the
full Definition 1.3 axiom package.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

noncomputable def stageModelFamilyPresentation_axioms
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
      |>.preFrobenioid.FrobenioidAxioms :=
  (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1).axioms

#check stageModelFamilyPresentation_axioms

end SourceFrobenioidSystem
end Iut
