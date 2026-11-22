/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelComponentSystemConsumer

/-!
# Consumer: connected base categories of the component system

Every base category of the assembled component system is connected.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

theorem stageModelComponentSystemConsumer_baseCategory_isConnected
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.IsConnected
      ((stageModelComponentSystemConsumer (K := K) Label).baseCategory index) := by
  simpa [stageModelComponentSystemConsumer, stageModelComponentBaseFamily] using
    (stageModelPresentationComponentFamily (K := K) Label index).connected

end SourceFrobenioidSystem
end Iut
