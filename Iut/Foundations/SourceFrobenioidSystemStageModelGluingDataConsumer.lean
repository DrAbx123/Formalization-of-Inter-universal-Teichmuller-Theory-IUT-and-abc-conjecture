/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingConsumer

/-!
# Consumers of place/label gluing data

1. `StageModelGluingData` itself: relation and categorical equivalences. -/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u} {G : Type u} [Group G]

namespace StageModelGluingData

/-- The gluing relation. -/
def relationAt (data : StageModelGluingData (K := K) Label)
    (source target : NumberField.FinitePlace K × Label) : Prop :=
  data.relation source target

@[simp] theorem relationAt_eq (data : StageModelGluingData (K := K) Label)
    (source target : NumberField.FinitePlace K × Label) :
    data.relationAt source target = data.relation source target :=
  rfl

/-- The categorical equivalence for a related pair. -/
def equivalenceAt (data : StageModelGluingData (K := K) Label)
    {source target : NumberField.FinitePlace K × Label}
    (related : data.relation source target) :
    CategoryTheory.Equivalence
      (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation
        source.1).baseCategory
      (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation
        target.1).baseCategory :=
  data.equivalence related

@[simp] theorem relationAt_trivial
    (source target : NumberField.FinitePlace K × Label) :
    (StageModelGluingData.trivial (K := K) Label).relationAt source target =
      (source = target) :=
  rfl

end StageModelGluingData

/-! ## 2. Projections from `StageModelSystemDataGluingConsumer` -/

namespace StageModelSystemDataGluingConsumer

def stageModelGluingData
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G) :
    StageModelGluingData (K := K) Label :=
  consumer.data.gluing

def stageModelSystemData
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G) :
    StageModelSystemData (K := K) Label :=
  consumer.data.system

def stageModelLabelActionData
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G) :
    StageModelLabelActionData Label G :=
  consumer.data.labelAction

@[simp] theorem stageModelGluingData_relation
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G)
    (source target : NumberField.FinitePlace K × Label) :
    (consumer.stageModelGluingData).relation source target =
      consumer.gluingRelation source target :=
  rfl

@[simp] theorem stageModelSystemData_presentation
    (consumer : StageModelSystemDataGluingConsumer (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    (consumer.stageModelSystemData).presentation index =
      consumer.presentation index :=
  rfl

end StageModelSystemDataGluingConsumer

#check StageModelGluingData.relationAt
#check StageModelGluingData.equivalenceAt
#check StageModelSystemDataGluingConsumer.stageModelGluingData
#check StageModelSystemDataGluingConsumer.stageModelSystemData
#check StageModelSystemDataGluingConsumer.stageModelLabelActionData

end SourceFrobenioidSystem
end Iut
