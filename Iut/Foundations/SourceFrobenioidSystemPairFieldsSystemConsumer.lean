/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsConsumer

/-!
# Consumer: actual system from pair fields

Converts the pair fields into an actual `FrobenioidSystem Bool`.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def toFrobenioidSystem
    (fields : PairFields) : FrobenioidSystem Bool where
  presentation := fields.presentation

@[simp] theorem toFrobenioidSystem_presentation
    (fields : PairFields) (index : Bool) :
    fields.toFrobenioidSystem.presentation index = fields.presentation index :=
  rfl

@[simp] theorem toFrobenioidSystem_baseCategory
    (fields : PairFields) (index : Bool) :
    fields.toFrobenioidSystem.baseCategory index = fields.base index :=
  (fields.base_eq index).symm

theorem toFrobenioidSystem_baseCategory_isConnected
    (fields : PairFields) (index : Bool) :
    CategoryTheory.IsConnected (fields.toFrobenioidSystem.baseCategory index) := by
  rw [toFrobenioidSystem_baseCategory]
  exact fields.connected index

noncomputable def toFrobenioidSystem_axioms
    (fields : PairFields) (index : Bool) :
    ((fields.toFrobenioidSystem).presentation index).preFrobenioid.FrobenioidAxioms :=
  fields.axioms index

end PairFields

#check PairFields.toFrobenioidSystem
#check PairFields.toFrobenioidSystem_baseCategory_isConnected
#check PairFields.toFrobenioidSystem_axioms

end FrobenioidSystem
end Iut
