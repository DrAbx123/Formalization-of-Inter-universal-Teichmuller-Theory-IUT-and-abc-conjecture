/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystem
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingConsumer

/-!
# Consumer: actual system of Frobenioids from place/label system data

Extracts the actual `FrobenioidSystem` carried by a
`StageModelSystemDataGluingConsumer`, together with its base categories and
axiom packages.  This is the system-level consumer of IUTchI, Definition
6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u} {G : Type u} [Group G]

namespace StageModelSystemDataGluingConsumer

noncomputable def toFrobenioidSystem
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G) :
    FrobenioidSystem (NumberField.FinitePlace K × Label) where
  presentation := fun index =>
    StageModelSystemDataGluingConsumer.presentation consumer index

@[simp] theorem toFrobenioidSystem_presentation
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    (toFrobenioidSystem consumer).presentation index =
      StageModelSystemDataGluingConsumer.presentation consumer index :=
  rfl

@[simp] theorem toFrobenioidSystem_baseCategory
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    (toFrobenioidSystem consumer).baseCategory index =
      StageModelSystemDataGluingConsumer.baseCategory consumer index :=
  (consumer.data.system.base_eq index).symm

theorem toFrobenioidSystem_baseCategory_isConnected
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.IsConnected
      ((toFrobenioidSystem consumer).baseCategory index) := by
  rw [toFrobenioidSystem_baseCategory]
  exact StageModelSystemDataGluingConsumer.baseCategory_isConnected consumer index

noncomputable def toFrobenioidSystem_axioms
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    ((toFrobenioidSystem consumer).presentation index)
      |>.preFrobenioid.FrobenioidAxioms :=
  StageModelSystemDataGluingConsumer.presentation_axioms consumer index

end StageModelSystemDataGluingConsumer

#check StageModelSystemDataGluingConsumer.toFrobenioidSystem
#check StageModelSystemDataGluingConsumer.toFrobenioidSystem_baseCategory_isConnected
#check StageModelSystemDataGluingConsumer.toFrobenioidSystem_axioms

end SourceFrobenioidSystem
end Iut
