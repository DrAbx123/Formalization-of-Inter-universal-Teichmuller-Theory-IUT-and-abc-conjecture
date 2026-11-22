/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemDataConsumer
import Iut.Foundations.SourceFrobenioidSystemGluingComposition

/-!
# Consumer: composed gluing of the pair-fields system data

Composes the data's gluing with itself on the actual two-component system.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def toSystemDataGluingComp
    (fields : PairFields) (G : Type) [Group G] :
    FrobenioidSystemGluing (toSystemData fields G).system :=
  (toSystemData fields G).gluing.comp (toSystemData fields G).gluing

theorem toSystemDataGluingComp_relation
    (fields : PairFields) (G : Type) [Group G]
    (source target : Bool) :
    (toSystemDataGluingComp fields G).relation source target ↔
      source = target := by
  constructor
  · intro related
    obtain ⟨middle, leftRelated, rightRelated⟩ := related
    exact leftRelated.trans rightRelated
  · intro related
    exact ⟨source, rfl, related⟩

end PairFields

#check PairFields.toSystemDataGluingComp
#check PairFields.toSystemDataGluingComp_relation

end FrobenioidSystem
end Iut

-- revived for blocked-tail sweep
