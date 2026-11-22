/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelComponentSystemFieldsSystemConsumer

/-!
# Consumer: base-category family of the fields-assembled system

Projects the base-category family of the actual system assembled from fields.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u}

namespace StageModelComponentSystemFields

noncomputable def systemBaseFamily
    (fields : StageModelComponentSystemFields (K := K) Label) :
    (index : NumberField.FinitePlace K × Label) -> CategoryTheory.Cat.{u, u} :=
  fun index => (fields.presentation index).baseCategory

@[simp] theorem systemBaseFamily_eq
    (fields : StageModelComponentSystemFields (K := K) Label)
    (index : NumberField.FinitePlace K × Label) :
    StageModelComponentSystemFields.systemBaseFamily fields index =
      fields.base index :=
  (fields.base_eq index).symm

theorem systemBaseFamily_isConnected
    (fields : StageModelComponentSystemFields (K := K) Label)
    (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.IsConnected
      (StageModelComponentSystemFields.systemBaseFamily fields index) := by
  rw [systemBaseFamily_eq]
  exact fields.connected index

end StageModelComponentSystemFields

#check StageModelComponentSystemFields.systemBaseFamily
#check StageModelComponentSystemFields.systemBaseFamily_isConnected

end SourceFrobenioidSystem
end Iut
