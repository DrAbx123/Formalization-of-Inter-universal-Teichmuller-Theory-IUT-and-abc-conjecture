/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModel
import Iut.Foundations.SourceFrobenioidSystemReindex

/-!
# Consumer: reindexed stage-model system

Reindexes the place/label stage-model system along an arbitrary map of index
types.  This is the Gluing-independent formal operation used by label
actions and place/label families (IUTchI, Definition 6.13, (i)).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable (Label : Type u) [Nonempty Label]

/-- Reindex the place/label stage-model system. -/
noncomputable def stageModelReindexConsumer
    {iota : Type u} (map : iota -> NumberField.FinitePlace K × Label) :
    FrobenioidSystem iota :=
  (stageModelLabeledFrobenioidSystem (K := K) Label).reindex map

@[simp] theorem stageModelReindexConsumer_presentation
    {iota : Type u} (map : iota -> NumberField.FinitePlace K × Label)
    (index : iota) :
    (stageModelReindexConsumer (K := K) Label map).presentation index =
      (stageModelLabeledFrobenioidSystem (K := K) Label).presentation (map index) :=
  rfl

#check stageModelReindexConsumer
#check stageModelReindexConsumer_presentation

end SourceFrobenioidSystem
end Iut
