/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemDataReindexedDataReindexDataConsumer
import Iut.Foundations.SourceFrobenioidSystemGluingComposition

/-!
# Consumer: composed gluing of the iterated-reindexed system data

Composes the data's identity gluing with itself.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def toSystemDataReindexedDataReindexDataGluingComp
    (fields : PairFields) (G : Type) [Group G] (g h : G) :
    FrobenioidSystemGluing
      (toSystemDataReindexedDataReindexData fields G g h).system :=
  (toSystemDataReindexedDataReindexData fields G g h).gluing.comp
    (toSystemDataReindexedDataReindexData fields G g h).gluing

theorem toSystemDataReindexedDataReindexDataGluingComp_relation
    (fields : PairFields) (G : Type) [Group G] (g h : G)
    (source target : Bool) :
    (toSystemDataReindexedDataReindexDataGluingComp fields G g h).relation
      source target ↔ source = target := by
  constructor
  · intro related
    obtain ⟨middle, leftRelated, rightRelated⟩ := related
    exact leftRelated.trans rightRelated
  · intro related
    exact ⟨source, rfl, related⟩

end PairFields

#check PairFields.toSystemDataReindexedDataReindexDataGluingComp
#check PairFields.toSystemDataReindexedDataReindexDataGluingComp_relation

end FrobenioidSystem
end Iut
