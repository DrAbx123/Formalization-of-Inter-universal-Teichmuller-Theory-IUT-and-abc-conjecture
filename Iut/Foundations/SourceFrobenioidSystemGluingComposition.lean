/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemGluing

/-!
# Composition of gluing data

Composition of the minimal gluing relations and of the associated categorical
equivalences.  This is the formal counterpart of composing the full
poly-isomorphisms that glue a system of Frobenioids (IUTchI, Definition
6.13, (i)).
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystemGluing

variable {iota : Type u} {system : FrobenioidSystem iota}

/-- Composite gluing data. -/
noncomputable def comp (left right : FrobenioidSystemGluing system) :
    FrobenioidSystemGluing system where
  relation := fun source target =>
    exists middle, left.relation source middle ∧ right.relation middle target
  equivalence := fun {source target} related => by
    classical
    let middle := Classical.choose related
    have leftRelated : left.relation source middle :=
      (Classical.choose_spec related).1
    have rightRelated : right.relation middle target :=
      (Classical.choose_spec related).2
    exact (left.equivalence leftRelated).trans (right.equivalence rightRelated)

@[simp] theorem comp_relation
    (left right : FrobenioidSystemGluing system) (source target : iota) :
    (left.comp right).relation source target ↔
      exists middle, left.relation source middle ∧ right.relation middle target :=
  Iff.rfl

end FrobenioidSystemGluing

#check FrobenioidSystemGluing.comp
#check FrobenioidSystemGluing.comp_relation

end Iut
