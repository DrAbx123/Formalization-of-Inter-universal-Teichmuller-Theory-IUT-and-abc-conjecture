/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingFieldsConsumer

/-!
# Consumer: base categories of the concrete place/label system

The base category of each component of the concrete finite-stage system is
the base category of the corresponding model Frobenioid.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

namespace StageModelSystemDataGluing

variable {Label : Type u} {G : Type u} [Group G]

theorem ofFiniteStage_baseCategory
    (index : NumberField.FinitePlace K × Label) :
    (ofFiniteStage (K := K) Label G).baseCategory index =
      (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
        |>.baseCategory :=
  rfl

theorem ofFiniteStage_baseCategory_isConnected
    (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.IsConnected
      ((ofFiniteStage (K := K) Label G).baseCategory index) :=
  (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
    |>.baseConnected

end StageModelSystemDataGluing

#check StageModelSystemDataGluing.ofFiniteStage_baseCategory
#check StageModelSystemDataGluing.ofFiniteStage_baseCategory_isConnected

end SourceFrobenioidSystem
end Iut
