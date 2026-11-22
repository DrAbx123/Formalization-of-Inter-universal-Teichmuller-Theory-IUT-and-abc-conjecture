/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsGluingConsumer
import Iut.Foundations.SourceFrobenioidSystemGluingComposition

/-!
# Consumer: composed gluing on the pair-fields system

The identity gluing composed with itself, on the actual two-component system.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def toFrobenioidSystemGluingComp
    (fields : PairFields) :
    FrobenioidSystemGluing (PairFields.toFrobenioidSystem fields) :=
  (toFrobenioidSystemGluing fields).comp (toFrobenioidSystemGluing fields)

theorem toFrobenioidSystemGluingComp_relation
    (fields : PairFields) (source target : Bool) :
    (toFrobenioidSystemGluingComp fields).relation source target ↔
      source = target := by
  constructor
  · intro related
    obtain ⟨middle, leftRelated, rightRelated⟩ := related
    exact leftRelated.trans rightRelated
  · intro related
    exact ⟨source, rfl, related⟩

end PairFields

#check PairFields.toFrobenioidSystemGluingComp
#check PairFields.toFrobenioidSystemGluingComp_relation

end FrobenioidSystem
end Iut
