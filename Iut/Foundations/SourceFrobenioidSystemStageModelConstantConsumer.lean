/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModel
import Iut.Foundations.SourceFrobenioidSystemConstant

/-!
# Consumer: constant stage-model system

Builds the constant system from the finite-stage model Frobenioid at a given
finite place.  Gluing-independent consumer of IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

/-- Constant system from one finite-stage model Frobenioid. -/
noncomputable def stageModelConstantConsumer
    (place : NumberField.FinitePlace K) (iota : Type u) :
    FrobenioidSystem iota :=
  FrobenioidSystem.constant
    (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation place) iota

@[simp] theorem stageModelConstantConsumer_presentation
    (place : NumberField.FinitePlace K) (iota : Type u) (index : iota) :
    (stageModelConstantConsumer (K := K) place iota).presentation index =
      SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation place :=
  rfl

#check stageModelConstantConsumer
#check stageModelConstantConsumer_presentation

end SourceFrobenioidSystem
end Iut
