/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Frobenioid axioms of the finite-stage model family

Each finite-place model Frobenioid has the full Definition 1.3 axiom package.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

noncomputable def stageAxioms (place : NumberField.FinitePlace K) :
    (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation place)
      |>.preFrobenioid.FrobenioidAxioms :=
  (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation place).axioms

#check stageAxioms

end SourceFrobenioidSystem
end Iut
