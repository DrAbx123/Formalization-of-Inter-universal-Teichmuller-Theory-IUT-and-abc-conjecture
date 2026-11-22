/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemDataLabelActionReindexGluingConsumer
import Iut.Foundations.SourceFrobenioidSystemGluingComposition

/-!
# Consumer: composed gluing on the label-reindexed system data

Composes the identity gluing on the reindexed system with itself.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def toSystemDataReindexedGluingComp
    (fields : PairFields) (G : Type) [Group G] (g : G) :
    FrobenioidSystemGluing
      (toSystemDataReindexed fields G g) :=
  (toSystemDataReindexedGluing fields G g).comp
    (toSystemDataReindexedGluing fields G g)

theorem toSystemDataReindexedGluingComp_relation
    (fields : PairFields) (G : Type) [Group G] (g : G)
    (source target : Bool) :
    (toSystemDataReindexedGluingComp fields G g).relation source target ↔
      source = target := by
  constructor
  · intro related
    obtain ⟨middle, leftRelated, rightRelated⟩ := related
    exact leftRelated.trans rightRelated
  · intro related
    exact ⟨source, rfl, related⟩

end PairFields

#check PairFields.toSystemDataReindexedGluingComp
#check PairFields.toSystemDataReindexedGluingComp_relation

end FrobenioidSystem
end Iut
