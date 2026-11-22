/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingLabelReindexBaseConsumer

/-!
# Consumer: gluing relation after label action

Transports the gluing relation along the label action on place/label indices.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u} {G : Type u} [Group G]

namespace StageModelSystemDataGluing

variable (data : StageModelSystemDataGluing (K := K) Label G)

/-- Gluing relation after acting by a label-group element. -/
def gluingRelationAtLabel (g : G)
    (source target : NumberField.FinitePlace K × Label) : Prop :=
  data.gluingRelation (data.applyLabel g source) (data.applyLabel g target)

@[simp] theorem gluingRelationAtLabel_eq (g : G)
    (source target : NumberField.FinitePlace K × Label) :
    data.gluingRelationAtLabel g source target =
      data.gluingRelation (data.applyLabel g source) (data.applyLabel g target) :=
  rfl

end StageModelSystemDataGluing

#check StageModelSystemDataGluing.gluingRelationAtLabel
#check StageModelSystemDataGluing.gluingRelationAtLabel_eq

end SourceFrobenioidSystem
end Iut
