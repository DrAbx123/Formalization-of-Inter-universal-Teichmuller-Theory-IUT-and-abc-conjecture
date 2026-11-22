/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelGluingDataConsumer

/-!
# Consumer: system of Frobenioids from the place/label gluing consumer

Extracts the actual `FrobenioidSystem` from a
`StageModelSystemDataGluingConsumer`, together with its base categories.
This is the system-level consumer of IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u} {G : Type u} [Group G]

namespace StageModelSystemDataGluingConsumer

/-- The actual system of Frobenioids carried by the consumer. -/
noncomputable def toFrobenioidSystem
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G) :
    FrobenioidSystem (NumberField.FinitePlace K × Label) where
  presentation := fun index => consumer.presentation index

@[simp] theorem toFrobenioidSystem_presentation
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    (consumer.toFrobenioidSystem).presentation index =
      consumer.presentation index :=
  rfl

@[simp] theorem toFrobenioidSystem_baseCategory
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    (consumer.toFrobenioidSystem).baseCategory index =
      consumer.baseCategory index :=
  rfl

theorem toFrobenioidSystem_baseCategory_isConnected
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.IsConnected
      ((consumer.toFrobenioidSystem).baseCategory index) :=
  consumer.baseCategory_isConnected index

theorem toFrobenioidSystem_presentation_axioms
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    ((consumer.toFrobenioidSystem).presentation index).preFrobenioid.FrobenioidAxioms :=
  consumer.presentation_axioms index

end StageModelSystemDataGluingConsumer

#check StageModelSystemDataGluingConsumer.toFrobenioidSystem
#check StageModelSystemDataGluingConsumer.toFrobenioidSystem_presentation
#check StageModelSystemDataGluingConsumer.toFrobenioidSystem_baseCategory_isConnected

end SourceFrobenioidSystem
end Iut
