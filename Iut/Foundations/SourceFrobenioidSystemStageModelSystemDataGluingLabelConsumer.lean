/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluing
import Iut.Foundations.SourceFrobenioidSystemStageModelLabelActionData

/-!
# Consumer: label action of place/label system data

Consumes `StageModelSystemDataGluing` and exposes its label action on the
place/label indices.  This completes the data-level consumer of IUTchI,
Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable (Label : Type u) (G : Type u) [Group G]

namespace StageModelSystemDataGluing

/-- The label action carried by the data. -/
def labelAction (data : StageModelSystemDataGluing (K := K) Label G) :
    StageModelLabelActionData Label G :=
  data.labelAction

/-- Apply a group element to a place/label index through the label action. -/
def applyLabel (data : StageModelSystemDataGluing (K := K) Label G)
    (g : G) (index : NumberField.FinitePlace K × Label) :
    NumberField.FinitePlace K × Label :=
  data.labelAction.apply g index

@[simp] theorem applyLabel_def (data : StageModelSystemDataGluing (K := K) Label G)
    (g : G) (index : NumberField.FinitePlace K × Label) :
    data.applyLabel g index = data.labelAction.apply g index :=
  rfl

end StageModelSystemDataGluing

#check StageModelSystemDataGluing.labelAction
#check StageModelSystemDataGluing.applyLabel

end SourceFrobenioidSystem
end Iut
