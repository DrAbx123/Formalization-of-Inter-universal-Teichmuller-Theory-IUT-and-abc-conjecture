/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataConsumer
import Iut.Foundations.SourceFrobenioidSystemSystemAxiomsConsumer

/-!
# Stage-model system axioms consumer

Consumes the place/label system data and the system axiom consumer, exposing
for each component the actual Frobenioid axiom package.  This is the
stage-model instance of the system axioms consumer of IUTchI, Definition
6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u}

/-- Axioms of a place/label component, consumed from the system data. -/
noncomputable def stageModelSystemAxiomsConsumer
    (data : StageModelSystemData (K := K) Label)
    (index : NumberField.FinitePlace K × Label) :
    ((data.toFrobenioidSystem).presentation index).preFrobenioid.FrobenioidAxioms :=
  (data.toFrobenioidSystem).systemAxiomsConsumer index

@[simp] theorem stageModelSystemAxiomsConsumer_eq
    (data : StageModelSystemData (K := K) Label)
    (index : NumberField.FinitePlace K × Label) :
    stageModelSystemAxiomsConsumer data index = data.axioms index :=
  rfl

#check stageModelSystemAxiomsConsumer
#check stageModelSystemAxiomsConsumer_eq

end SourceFrobenioidSystem
end Iut
