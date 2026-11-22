/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingActual

/-!
# Composition of actual place/label system bundles

Composes the gluing relations of two actual system bundles on the same
underlying system; the label action is that of the left bundle.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u} {G : Type u} [Group G]

/-- Transport an equivalence along equalities of Cat objects. -/
private noncomputable def castEquivalence
    {C D C' D' : CategoryTheory.Cat.{u, u}}
    (e : CategoryTheory.Equivalence C D)
    (hC : C = C') (hD : D = D') :
    CategoryTheory.Equivalence C' D' :=
  (eqToEquivalenceCat hC.symm).trans
    (e.trans (eqToEquivalenceCat hD))

namespace StageModelSystemDataGluingActual

noncomputable def comp
    (left right : StageModelSystemDataGluingActual (K := K) Label G)
    (system_eq : left.system = right.system) :
    StageModelSystemDataGluingActual (K := K) Label G where
  system := left.system
  relation := fun source target =>
    exists middle, left.relation source middle ∧ right.relation middle target
  equivalence := fun {source target} related => by
    classical
    let middle := Classical.choose related
    have leftRelated : left.relation source middle :=
      (Classical.choose_spec related).1
    have rightRelated : right.relation middle target :=
      (Classical.choose_spec related).2
    have hMiddle :
        left.system.baseCategory middle = right.system.baseCategory middle :=
      congrArg (fun system => system.baseCategory middle) system_eq
    have hTarget :
        left.system.baseCategory target = right.system.baseCategory target :=
      congrArg (fun system => system.baseCategory target) system_eq
    exact (left.equivalence leftRelated).trans
      (castEquivalence (right.equivalence rightRelated)
        hMiddle.symm hTarget.symm)
  labelAction := left.labelAction

@[simp] theorem comp_system
    (left right : StageModelSystemDataGluingActual (K := K) Label G)
    (system_eq : left.system = right.system) :
    (left.comp right system_eq).system = left.system :=
  rfl

@[simp] theorem comp_labelAction
    (left right : StageModelSystemDataGluingActual (K := K) Label G)
    (system_eq : left.system = right.system) :
    (left.comp right system_eq).labelAction = left.labelAction :=
  rfl

theorem comp_relation
    (left right : StageModelSystemDataGluingActual (K := K) Label G)
    (system_eq : left.system = right.system)
    (source target : NumberField.FinitePlace K × Label) :
    (left.comp right system_eq).relation source target ↔
      exists middle,
        left.relation source middle ∧ right.relation middle target :=
  Iff.rfl

noncomputable def comp_equivalence
    (left right : StageModelSystemDataGluingActual (K := K) Label G)
    (system_eq : left.system = right.system)
    {source target : NumberField.FinitePlace K × Label}
    (related : (left.comp right system_eq).relation source target) :
    CategoryTheory.Equivalence (left.system.baseCategory source)
      (left.system.baseCategory target) :=
  (left.comp right system_eq).equivalence related

end StageModelSystemDataGluingActual

#check StageModelSystemDataGluingActual.comp
#check StageModelSystemDataGluingActual.comp_relation
#check StageModelSystemDataGluingActual.comp_equivalence

end SourceFrobenioidSystem
end Iut
