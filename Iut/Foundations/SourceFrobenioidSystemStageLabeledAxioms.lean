/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Place/label Frobenioid axioms of the finite-stage model family

Every place/label component carries the full Definition 1.3 axiom package.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

noncomputable def stageLabeledAxioms
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
      |>.preFrobenioid.FrobenioidAxioms :=
  (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1).axioms

#check stageLabeledAxioms

end SourceFrobenioidSystem
end Iut
