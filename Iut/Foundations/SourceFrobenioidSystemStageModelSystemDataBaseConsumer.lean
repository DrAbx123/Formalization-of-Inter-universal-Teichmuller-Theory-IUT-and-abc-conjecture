/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataConsumer

/-!
# Consumer: base categories of the place/label system data

Projects the base category and connectedness of each component from a
`StageModelSystemData` via its extracted system of Frobenioids.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u}

namespace StageModelSystemData

noncomputable def baseCategoryConsumer
    (data : StageModelSystemData (K := K) Label)
    (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.Cat.{u, u} :=
  data.toFrobenioidSystem.baseCategory index

@[simp] theorem baseCategoryConsumer_eq
    (data : StageModelSystemData (K := K) Label)
    (index : NumberField.FinitePlace K × Label) :
    data.baseCategoryConsumer index = data.base index :=
  (data.base_eq index).symm

theorem baseCategoryConsumer_isConnected
    (data : StageModelSystemData (K := K) Label)
    (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.IsConnected (data.baseCategoryConsumer index) :=
  data.base_connected index

end StageModelSystemData

#check StageModelSystemData.baseCategoryConsumer
#check StageModelSystemData.baseCategoryConsumer_eq
#check StageModelSystemData.baseCategoryConsumer_isConnected

end SourceFrobenioidSystem
end Iut
