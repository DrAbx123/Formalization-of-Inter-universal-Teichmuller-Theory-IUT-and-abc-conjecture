/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelComponentSystemConsumer

/-!
# Consumer: base-category family of the component system

Projects the base categories of the assembled system of Frobenioids.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

noncomputable def stageModelComponentSystemBaseFamily
    (Label : Type u) :
    (index : NumberField.FinitePlace K × Label) -> CategoryTheory.Cat.{u, u} :=
  fun index => (stageModelComponentSystemConsumer (K := K) Label).baseCategory index

@[simp] theorem stageModelComponentSystemBaseFamily_eq
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    stageModelComponentSystemBaseFamily (K := K) Label index =
      stageModelComponentBaseFamily (K := K) Label index :=
  rfl

end SourceFrobenioidSystem
end Iut
