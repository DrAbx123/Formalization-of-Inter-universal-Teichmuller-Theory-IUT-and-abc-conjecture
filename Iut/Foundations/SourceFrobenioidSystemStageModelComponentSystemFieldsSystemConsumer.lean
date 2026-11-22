/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelComponentSystemFieldsConsumer

/-!
# Consumer: system of Frobenioids from component-system fields

Converts the packaged component-system fields into an actual
`FrobenioidSystem`.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u}

namespace StageModelComponentSystemFields

noncomputable def toFrobenioidSystem
    (fields : StageModelComponentSystemFields (K := K) Label) :
    FrobenioidSystem (NumberField.FinitePlace K × Label) where
  presentation := fields.presentation

@[simp] theorem toFrobenioidSystem_presentation
    (fields : StageModelComponentSystemFields (K := K) Label)
    (index : NumberField.FinitePlace K × Label) :
    fields.toFrobenioidSystem.presentation index = fields.presentation index :=
  rfl

@[simp] theorem toFrobenioidSystem_baseCategory
    (fields : StageModelComponentSystemFields (K := K) Label)
    (index : NumberField.FinitePlace K × Label) :
    fields.toFrobenioidSystem.baseCategory index = fields.base index :=
  (fields.base_eq index).symm

theorem toFrobenioidSystem_baseCategory_isConnected
    (fields : StageModelComponentSystemFields (K := K) Label)
    (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.IsConnected (fields.toFrobenioidSystem.baseCategory index) := by
  rw [toFrobenioidSystem_baseCategory]
  exact fields.connected index

end StageModelComponentSystemFields

#check StageModelComponentSystemFields.toFrobenioidSystem
#check StageModelComponentSystemFields.toFrobenioidSystem_baseCategory_isConnected

end SourceFrobenioidSystem
end Iut
