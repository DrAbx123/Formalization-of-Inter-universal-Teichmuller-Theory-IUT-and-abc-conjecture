/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluing
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataConsumer

/-!
# Consumer: system + gluing from place/label system data

Consumes `StageModelSystemDataGluing` and exposes the actual system of
Frobenioids, its base-category family, and the gluing relation.  This is the
data-level consumer of IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u} {G : Type u} [Group G]

namespace StageModelSystemDataGluing

/-- The actual Frobenioid system carried by the data. -/
noncomputable def toFrobenioidSystem
    (data : StageModelSystemDataGluing (K := K) Label G) :
    FrobenioidSystem (NumberField.FinitePlace K × Label) :=
  data.system.toFrobenioidSystem

@[simp] theorem toFrobenioidSystem_presentation
    (data : StageModelSystemDataGluing (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    data.toFrobenioidSystem.presentation index =
      data.system.presentation index :=
  rfl

/-- The gluing relation carried by the data. -/
def gluingRelation
    (data : StageModelSystemDataGluing (K := K) Label G)
    (source target : NumberField.FinitePlace K × Label) : Prop :=
  data.gluing.relation source target

@[simp] theorem gluingRelation_eq
    (data : StageModelSystemDataGluing (K := K) Label G)
    (source target : NumberField.FinitePlace K × Label) :
    data.gluingRelation source target = data.gluing.relation source target :=
  rfl

end StageModelSystemDataGluing

#check StageModelSystemDataGluing.toFrobenioidSystem
#check StageModelSystemDataGluing.gluingRelation

end SourceFrobenioidSystem
end Iut
