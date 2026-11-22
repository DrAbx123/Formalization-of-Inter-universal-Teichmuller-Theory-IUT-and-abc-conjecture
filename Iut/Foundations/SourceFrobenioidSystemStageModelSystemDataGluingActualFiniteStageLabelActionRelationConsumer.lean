/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingActualFiniteStageLabelActionConsumer

/-!
# Consumer: label action preserves the finite-stage gluing relation

The finite-stage actual bundle has trivial label action, hence its identity
gluing relation is label-action invariant.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

namespace StageModelSystemDataGluingActual

theorem finiteStageActual_relation_labelAction
    (Label : Type u) (G : Type u) [Group G] (g : G)
    (source target : NumberField.FinitePlace K × Label) :
    (ofFiniteStageActual (K := K) Label G).relation
      ((ofFiniteStageActual (K := K) Label G).labelAction g source)
      ((ofFiniteStageActual (K := K) Label G).labelAction g target) ↔
    (ofFiniteStageActual (K := K) Label G).relation source target := by
  simp [finiteStageActual_relation, finiteStageActual_labelAction_apply]

end StageModelSystemDataGluingActual

#check StageModelSystemDataGluingActual.finiteStageActual_relation_labelAction

end SourceFrobenioidSystem
end Iut
