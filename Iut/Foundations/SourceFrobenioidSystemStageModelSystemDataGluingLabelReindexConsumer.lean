/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingLabelConsumer
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataConsumer
import Iut.Foundations.SourceFrobenioidSystemReindex

/-!
# Consumer: reindexing by the label action

Moves the place/label system along a label-group element by reindexing its

underlying system of Frobenioids.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u} {G : Type u} [Group G]

namespace StageModelSystemDataGluing

variable (data : StageModelSystemDataGluing (K := K) Label G)

/-- The system reindexed by a label-group element. -/
noncomputable def reindexedSystem (g : G) :
    FrobenioidSystem (NumberField.FinitePlace K × Label) :=
  data.system.toFrobenioidSystem.reindex (fun index => data.applyLabel g index)

@[simp] theorem reindexedSystem_presentation
    (g : G) (index : NumberField.FinitePlace K × Label) :
    (data.reindexedSystem g).presentation index =
      data.system.presentation (data.applyLabel g index) :=
  rfl

end StageModelSystemDataGluing

#check StageModelSystemDataGluing.reindexedSystem
#check StageModelSystemDataGluing.reindexedSystem_presentation

end SourceFrobenioidSystem
end Iut
