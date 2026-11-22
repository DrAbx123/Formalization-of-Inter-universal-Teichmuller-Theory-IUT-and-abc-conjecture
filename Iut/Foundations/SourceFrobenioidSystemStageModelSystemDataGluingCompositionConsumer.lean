/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingComposition
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingConsumerSystem

/-!
# Consumer: composed place/label system data

Wraps the composed data as a consumer and extracts its actual system of
Frobenioids.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u} {G : Type u} [Group G]

namespace StageModelSystemDataGluing

noncomputable def toConsumer
    (left right : StageModelSystemDataGluing (K := K) Label G) :
    StageModelSystemDataGluingConsumer (K := K) Label G where
  data := left.comp right

@[simp] theorem toConsumer_data
    (left right : StageModelSystemDataGluing (K := K) Label G) :
    (left.toConsumer right).data = left.comp right :=
  rfl

noncomputable def compToFrobenioidSystem
    (left right : StageModelSystemDataGluing (K := K) Label G) :
    FrobenioidSystem (NumberField.FinitePlace K × Label) :=
  StageModelSystemDataGluingConsumer.toFrobenioidSystem (left.toConsumer right)

@[simp] theorem compToFrobenioidSystem_presentation
    (left right : StageModelSystemDataGluing (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    (left.compToFrobenioidSystem right).presentation index =
      StageModelSystemDataGluingConsumer.presentation (left.toConsumer right) index :=
  rfl

theorem toConsumer_gluingRelation
    (left right : StageModelSystemDataGluing (K := K) Label G)
    (source target : NumberField.FinitePlace K × Label) :
    StageModelSystemDataGluingConsumer.gluingRelation (left.toConsumer right)
      source target ↔
      exists middle,
        left.gluing.relation source middle ∧ right.gluing.relation middle target :=
  Iff.rfl

end StageModelSystemDataGluing

noncomputable def compToFrobenioidSystem_axioms
    (left right : StageModelSystemDataGluing (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    ((left.compToFrobenioidSystem right).presentation index)
      |>.preFrobenioid.FrobenioidAxioms :=
  ((left.compToFrobenioidSystem right).presentation index).axioms

#check StageModelSystemDataGluing.toConsumer
#check StageModelSystemDataGluing.compToFrobenioidSystem
#check StageModelSystemDataGluing.toConsumer_gluingRelation

end SourceFrobenioidSystem
end Iut
