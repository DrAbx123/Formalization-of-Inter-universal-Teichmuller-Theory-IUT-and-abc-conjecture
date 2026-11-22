/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluing
import Iut.Foundations.SourceFrobenioidSystemStageModelGluingComposition

/-!
# Composition of place/label system data with gluing

Composes the data-level gluing of two systems while keeping the system data
and label action.  This is the composition operation on the data of IUTchI,
Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u} {G : Type u} [Group G]

namespace StageModelSystemDataGluing

/-- Compose the data-level gluing of two system data packages. -/
noncomputable def comp
    (left right : StageModelSystemDataGluing (K := K) Label G) :
    StageModelSystemDataGluing (K := K) Label G where
  system := left.system
  gluing := StageModelGluingData.comp (K := K) left.gluing right.gluing
  labelAction := left.labelAction
  compat := left.compat

@[simp] theorem comp_system
    (left right : StageModelSystemDataGluing (K := K) Label G) :
    (left.comp right).system = left.system :=
  rfl

@[simp] theorem comp_gluing
    (left right : StageModelSystemDataGluing (K := K) Label G) :
    (left.comp right).gluing =
      StageModelGluingData.comp (K := K) left.gluing right.gluing :=
  rfl

@[simp] theorem comp_labelAction
    (left right : StageModelSystemDataGluing (K := K) Label G) :
    (left.comp right).labelAction = left.labelAction :=
  rfl

theorem comp_relation
    (left right : StageModelSystemDataGluing (K := K) Label G)
    (source target : NumberField.FinitePlace K × Label) :
    (left.comp right).gluing.relation source target ↔
      exists middle,
        left.gluing.relation source middle ∧ right.gluing.relation middle target :=
  Iff.rfl

@[simp] theorem comp_ofFiniteStage_gluing
    (Label : Type u) (G : Type u) [Group G] :
    ((ofFiniteStage (K := K) Label G).comp (ofFiniteStage (K := K) Label G)).gluing =
      StageModelGluingData.comp (K := K)
        (StageModelGluingData.trivial (K := K) Label)
        (StageModelGluingData.trivial (K := K) Label) :=
  rfl

end StageModelSystemDataGluing

#check StageModelSystemDataGluing.comp
#check StageModelSystemDataGluing.comp_relation
#check StageModelSystemDataGluing.comp_ofFiniteStage_gluing

end SourceFrobenioidSystem
end Iut
