/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModel

/-!
# Frobenioid axioms for the stage-model system

Every finite-place/label component of the stage-model system satisfies the
full Frobenioid axiom package of Frobenioids I, Definition 1.3, via the
packaged `stageModelFrobenioidPresentation`.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable (Label : Type u) [Nonempty Label]

noncomputable def stageModelLabeledFrobenioidSystem_axioms
    (index : NumberField.FinitePlace K × Label) :
    ((stageModelLabeledFrobenioidSystem (K := K) Label).presentation index)
      |>.preFrobenioid.FrobenioidAxioms :=
  ((stageModelLabeledFrobenioidSystem (K := K) Label).presentation index).axioms

#check stageModelLabeledFrobenioidSystem_axioms

end SourceFrobenioidSystem
end Iut
