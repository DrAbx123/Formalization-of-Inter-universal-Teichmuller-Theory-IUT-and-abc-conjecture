/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingActualFiniteStage

/-!
# Consumer: trivial label action of the finite-stage actual instance

The concrete finite-stage actual instance has trivial label poly-action.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

namespace StageModelSystemDataGluingActual

theorem finiteStageActual_labelAction_apply
    (Label : Type u) (G : Type u) [Group G] (g : G)
    (index : NumberField.FinitePlace K × Label) :
    (ofFiniteStageActual (K := K) Label G).labelAction g index = index := by
  rcases index with ⟨place, label⟩
  rfl

end StageModelSystemDataGluingActual

#check StageModelSystemDataGluingActual.finiteStageActual_labelAction_apply

end SourceFrobenioidSystem
end Iut
