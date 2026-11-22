/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelGluingData

/-!
# Composition of place/label gluing data

Composition of the minimal gluing data on the place/label model family.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

namespace StageModelGluingData

variable {Label : Type u}

/-- Composition of gluing data. -/
noncomputable def comp (left right : StageModelGluingData (K := K) Label) :
    StageModelGluingData (K := K) Label where
  relation := fun source target =>
    exists middle, left.relation source middle ∧ right.relation middle target
  equivalence := fun {source target} related => by
    classical
    let middle := Classical.choose related
    have leftRelated : left.relation source middle :=
      (Classical.choose_spec related).1
    have rightRelated : right.relation middle target :=
      (Classical.choose_spec related).2
    exact (left.equivalence leftRelated).trans (right.equivalence rightRelated)

end StageModelGluingData

#check StageModelGluingData.comp

end SourceFrobenioidSystem
end Iut
