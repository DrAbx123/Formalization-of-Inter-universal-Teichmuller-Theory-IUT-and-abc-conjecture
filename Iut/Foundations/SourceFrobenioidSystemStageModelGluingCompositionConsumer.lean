/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelGluingComposition

/-!
# Consumer: composition of place/label gluing data

Exposes the composed gluing relation of the place/label model family and its
two-step factorization.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u}

namespace StageModelGluingData

/-- The relation of a composite gluing. -/
def compRelation (left right : StageModelGluingData (K := K) Label)
    (source target : NumberField.FinitePlace K × Label) : Prop :=
  (StageModelGluingData.comp (K := K) left right).relation source target

theorem compRelation_iff (left right : StageModelGluingData (K := K) Label)
    (source target : NumberField.FinitePlace K × Label) :
    compRelation left right source target ↔
      exists middle,
        left.relation source middle ∧ right.relation middle target :=
  Iff.rfl

end StageModelGluingData

#check StageModelGluingData.compRelation
#check StageModelGluingData.compRelation_iff

end SourceFrobenioidSystem
end Iut
