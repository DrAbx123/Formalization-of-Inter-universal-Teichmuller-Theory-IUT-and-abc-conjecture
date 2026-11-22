/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelPolyActionLawConsumer
import Iut.Foundations.SourceFrobenioidSystemStageModelReindexConsumer

/-!
# Consumer: stage-model system reindexed by the label action

Moves the place/label stage-model system by a label-group element, using the
trivial label action and reindexing.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable (Label : Type u) [Nonempty Label]

/-- Reindex the stage-model system by a label-group element. -/
noncomputable def stageModelLabelReindexedSystem
    (G : Type u) [Group G] (g : G) :
    FrobenioidSystem (NumberField.FinitePlace K × Label) :=
  (stageModelLabeledFrobenioidSystem (K := K) Label).reindex
    (fun index => stageModelLabelActionConsumer (K := K) Label G g index)

@[simp] theorem stageModelLabelReindexedSystem_presentation
    (G : Type u) [Group G] (g : G)
    (index : NumberField.FinitePlace K × Label) :
    (stageModelLabelReindexedSystem (K := K) Label G g).presentation index =
      (stageModelLabeledFrobenioidSystem (K := K) Label).presentation index :=
  rfl

@[simp] theorem stageModelLabelReindexedSystem_baseCategory
    (G : Type u) [Group G] (g : G)
    (index : NumberField.FinitePlace K × Label) :",
    (stageModelLabelReindexedSystem (K := K) Label G g).baseCategory index =",
      (stageModelLabeledFrobenioidSystem (K := K) Label).baseCategory index :=
  rfl

theorem stageModelLabelReindexedSystem_baseCategory_isConnected
    (G : Type u) [Group G] (g : G)
    (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.IsConnected
      ((stageModelLabelReindexedSystem (K := K) Label G g).baseCategory index) :=
  (stageModelLabeledFrobenioidSystem (K := K) Label).baseCategory_isConnected index

noncomputable def stageModelLabelReindexedSystem_axioms
    (G : Type u) [Group G] (g : G)
    (index : NumberField.FinitePlace K × Label) :
    ((stageModelLabelReindexedSystem (K := K) Label G g).presentation index)
      |>.preFrobenioid.FrobenioidAxioms :=
  ((stageModelLabelReindexedSystem (K := K) Label G g).presentation index).axioms

#check stageModelLabelReindexedSystem
#check stageModelLabelReindexedSystem_presentation

end SourceFrobenioidSystem
end Iut
