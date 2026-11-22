/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Connectedness of the place/label model base categories

Each base category of the finite-stage model family is connected.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

theorem stageModelFamilyBase_isConnected
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.IsConnected
      ((SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
        |>.baseCategory) :=
  (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
    |>.baseConnected

#check stageModelFamilyBase_isConnected

end SourceFrobenioidSystem
end Iut
