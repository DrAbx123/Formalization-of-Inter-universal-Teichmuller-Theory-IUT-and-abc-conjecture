/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingActualFiniteStage
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingActualComposition

/-!
# Consumer: composition of the finite-stage actual instance

Composes the concrete finite-stage actual bundle with itself; the composed
gluing relation is again equality of place/label indices.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

namespace StageModelSystemDataGluingActual

noncomputable def finiteStageActualComp
    (Label : Type u) (G : Type u) [Group G] :
    StageModelSystemDataGluingActual (K := K) Label G :=
  (ofFiniteStageActual (K := K) Label G).comp
    (ofFiniteStageActual (K := K) Label G) rfl

theorem finiteStageActualComp_relation
    (Label : Type u) (G : Type u) [Group G]
    (source target : NumberField.FinitePlace K × Label) :
    (finiteStageActualComp (K := K) Label G).relation source target ↔
      source = target := by
  rw [finiteStageActualComp, comp_relation]
  constructor
  · intro h
    obtain ⟨middle, leftRelated, rightRelated⟩ := h
    rw [finiteStageActual_relation] at leftRelated rightRelated
    exact leftRelated.trans rightRelated
  · intro h
    exact ⟨source, by rw [finiteStageActual_relation],
      by rw [finiteStageActual_relation]; exact h⟩

end StageModelSystemDataGluingActual

#check StageModelSystemDataGluingActual.finiteStageActualComp
#check StageModelSystemDataGluingActual.finiteStageActualComp_relation

end SourceFrobenioidSystem
end Iut
