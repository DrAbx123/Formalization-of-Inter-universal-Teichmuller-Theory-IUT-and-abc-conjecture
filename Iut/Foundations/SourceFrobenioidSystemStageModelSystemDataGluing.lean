/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemData
import Iut.Foundations.SourceFrobenioidSystemStageModelGluingData
import Iut.Foundations.SourceFrobenioidSystemStageModelLabelActionData

/-!
# Place/label system data with gluing and label action

Packages the place/label model system data together with its data-level
gluing and label action.  This is the closest self-contained formal
counterpart of the system of Frobenioids + poly-action of IUTchI,
Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

/-- Place/label system data with gluing and label action. -/
structure StageModelSystemDataGluing
    (Label : Type u) (G : Type u) [Group G] where
  system : StageModelSystemData (K := K) Label
  gluing : StageModelGluingData (K := K) Label
  labelAction : StageModelLabelActionData Label G
  compat :
    forall index,
      (system.presentation index).baseCategory =
        (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation
          index.1).baseCategory

namespace StageModelSystemDataGluing

/-- The concrete finite-stage instance. -/
noncomputable def ofFiniteStage (Label : Type u) (G : Type u) [Group G] :
    StageModelSystemDataGluing (K := K) Label G where
  system := StageModelSystemData.ofFiniteStage (K := K) Label
  gluing := StageModelGluingData.trivial (K := K) Label
  labelAction := { action := 1 }
  compat := fun index => rfl

end StageModelSystemDataGluing

#check StageModelSystemDataGluing
#check StageModelSystemDataGluing.ofFiniteStage

end SourceFrobenioidSystem
end Iut
