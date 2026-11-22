/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingActual
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluing

/-!
# Actual finite-stage place/label system with gluing and label action

The concrete finite-stage instance of the actual system, gluing relation, and
trivial label action.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

namespace StageModelSystemDataGluingActual

noncomputable def ofFiniteStageActual
    (Label : Type u) (G : Type u) [Group G] :
    StageModelSystemDataGluingActual (K := K) Label G :=
  StageModelSystemDataGluingActual.ofData
    (Label := Label) (G := G)
    { data := StageModelSystemDataGluing.ofFiniteStage (K := K) Label G }

noncomputable def finiteStageSystem
    (Label : Type u) (G : Type u) [Group G] :
    FrobenioidSystem (NumberField.FinitePlace K × Label) :=
  (ofFiniteStageActual (K := K) Label G).system

@[simp] theorem finiteStageSystem_presentation
    (Label : Type u) (G : Type u) [Group G]
    (index : NumberField.FinitePlace K × Label) :
    (finiteStageSystem (K := K) Label G).presentation index =
      SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1 := by
  simp [finiteStageSystem, ofFiniteStageActual,
    StageModelSystemDataGluingActual.ofData,
    StageModelSystemDataGluingConsumer.toFrobenioidSystem,
    StageModelSystemDataGluingConsumer.presentation,
    StageModelSystemDataGluing.ofFiniteStage,
    StageModelSystemData.ofFiniteStage,
    StageModelSystemData.ofFiniteStage_presentation]

theorem finiteStageActual_relation
    (Label : Type u) (G : Type u) [Group G]
    (source target : NumberField.FinitePlace K × Label) :
    (ofFiniteStageActual (K := K) Label G).relation source target ↔
      source = target := by
  simp [ofFiniteStageActual, StageModelSystemDataGluingActual.ofData,
    StageModelSystemDataGluingConsumer.gluingRelation,
    StageModelSystemDataGluing.ofFiniteStage, StageModelGluingData.trivial]

end StageModelSystemDataGluingActual

#check StageModelSystemDataGluingActual.ofFiniteStageActual
#check StageModelSystemDataGluingActual.finiteStageSystem
#check StageModelSystemDataGluingActual.finiteStageActual_relation

end SourceFrobenioidSystem
end Iut
