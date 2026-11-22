/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModel
import Iut.Foundations.SourceFrobenioidSystemBaseCategory

/-!
# Base categories of the stage-model system

Each place/label component of the finite-stage model system has a connected
base category.  This is the connectedness half of the system of base
categories associated to a system of Frobenioids (IUTchI, Definition 6.13,
(i)).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable (Label : Type u) [Nonempty Label]

theorem stageModelLabeledBaseCategory_isConnected
    (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.IsConnected
      ((stageModelLabeledFrobenioidSystem (K := K) Label).baseCategoryFamily index) :=
  (stageModelLabeledFrobenioidSystem (K := K) Label).baseCategoryFamily_isConnected index

#check stageModelLabeledBaseCategory_isConnected

end SourceFrobenioidSystem
end Iut
