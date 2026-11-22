/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystem

/-!
# Poly-action on the labels of a system of Frobenioids

IUTchI, Definition 6.13, (i), equips the system of Frobenioids with
F_l^{+-} / F_l^{*} poly-actions on the labels.  This file lands the
label-action part of that structure: a group action on the index type of
a `FrobenioidSystem`.
-/

open CategoryTheory

namespace Iut

universe u

structure FrobenioidSystemPolyAction {iota : Type u}
    (system : FrobenioidSystem iota) (G : Type u) [Group G] where
  labelAction : G →* Equiv.Perm iota

namespace FrobenioidSystemPolyAction

variable {iota : Type u} {system : FrobenioidSystem iota}
variable {G : Type u} [Group G]

@[simp] theorem labelAction_one (action : FrobenioidSystemPolyAction system G)
    (index : iota) :
    action.labelAction 1 index = index := by
  change action.labelAction 1 index = index
  rw [map_one]
  rfl

@[simp] theorem labelAction_mul
    (action : FrobenioidSystemPolyAction system G) (g h : G) (index : iota) :
    action.labelAction (g * h) index =
      action.labelAction g (action.labelAction h index) := by
  rw [map_mul]
  rfl

/-- The trivial poly-action of any group on any system. -/
def trivial (system : FrobenioidSystem iota) (G : Type u) [Group G] :
    FrobenioidSystemPolyAction system G where
  labelAction := 1

end FrobenioidSystemPolyAction

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

/-- The trivial label action on the finite-place stage-model system. -/
noncomputable def stageModelTrivialPolyAction
    (G : Type u) [Group G] :
    FrobenioidSystemPolyAction
      (SourceFrobenioidSystem.stageModelFrobenioidSystem (K := K)) G :=
  FrobenioidSystemPolyAction.trivial _ G

#check FrobenioidSystemPolyAction
#check FrobenioidSystemPolyAction.trivial
#check SourceFrobenioidSystem.stageModelTrivialPolyAction

end SourceFrobenioidSystem
end Iut
