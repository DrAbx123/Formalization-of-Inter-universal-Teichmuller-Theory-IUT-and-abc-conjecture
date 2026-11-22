/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingSystemConsumer

/-!
# Consumer: trivial gluing of the concrete place/label system

The concrete finite-stage system uses the identity gluing; its relation is
equality of place/label indices.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u} {G : Type u} [Group G]

namespace StageModelSystemDataGluing

theorem ofFiniteStage_gluingRelation
    (Label : Type u) (G : Type u) [Group G]
    (source target : NumberField.FinitePlace K × Label) :
    (ofFiniteStage (K := K) Label G).gluingRelation source target ↔
      source = target :=
  Iff.rfl

end StageModelSystemDataGluing

#check StageModelSystemDataGluing.ofFiniteStage_gluingRelation

end SourceFrobenioidSystem
end Iut
