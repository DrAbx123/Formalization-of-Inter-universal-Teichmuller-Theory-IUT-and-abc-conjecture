/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemData

/-!
# Consumer: system of Frobenioids from place/label system data

Extracts the actual `FrobenioidSystem` from a `StageModelSystemData`, together
with its base-category family.  This is the consumer-facing system object of
IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u}

namespace StageModelSystemData

/-- The actual system of Frobenioids carried by the data. -/
noncomputable def toFrobenioidSystem
    (data : StageModelSystemData (K := K) Label) :
    FrobenioidSystem (NumberField.FinitePlace K × Label) where
  presentation := data.presentation

@[simp] theorem toFrobenioidSystem_presentation
    (data : StageModelSystemData (K := K) Label)
    (index : NumberField.FinitePlace K × Label) :
    data.toFrobenioidSystem.presentation index = data.presentation index :=
  rfl

@[simp] theorem toFrobenioidSystem_baseCategory
    (data : StageModelSystemData (K := K) Label)
    (index : NumberField.FinitePlace K × Label) :
    data.toFrobenioidSystem.baseCategory index = data.base index :=
  (data.base_eq index).symm

end StageModelSystemData

#check StageModelSystemData.toFrobenioidSystem
#check StageModelSystemData.toFrobenioidSystem_presentation
#check StageModelSystemData.toFrobenioidSystem_baseCategory

end SourceFrobenioidSystem
end Iut
