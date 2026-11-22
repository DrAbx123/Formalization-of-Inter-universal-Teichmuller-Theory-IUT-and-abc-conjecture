/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModel
import Iut.Foundations.SourceFrobenioidSystemGluing
import Iut.Foundations.SourceFrobenioidSystemPolyAction

/-!
# Trivial gluing and label action for the stage-model system

The finite-place/label family of stage-model Frobenioids carries its identity
gluing and the trivial label action.  This is an actual data-level instance
of the system structure of IUTchI, Definition 6.13, (i); nontrivial gluing
and F_l^{+-}/F_l^{*} actions remain future work.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable (Label : Type u) [Nonempty Label]

/-- Identity gluing on the place/label stage-model system. -/
noncomputable def stageModelLabeledGluing :
    FrobenioidSystemGluing
      (stageModelLabeledFrobenioidSystem (K := K) Label) :=
  FrobenioidSystemGluing.trivial _

/-- Trivial label action on the place/label stage-model system. -/
noncomputable def stageModelLabeledPolyAction
    (G : Type u) [Group G] :
    FrobenioidSystemPolyAction
      (stageModelLabeledFrobenioidSystem (K := K) Label) G :=
  FrobenioidSystemPolyAction.trivial _ G

#check stageModelLabeledGluing
#check stageModelLabeledPolyAction

end SourceFrobenioidSystem
end Iut
