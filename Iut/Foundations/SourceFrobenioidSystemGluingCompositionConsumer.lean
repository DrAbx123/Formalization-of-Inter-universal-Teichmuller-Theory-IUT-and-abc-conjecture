/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemGluingComposition

/-!
# Consumer: composition of gluing data

Exposes the composed gluing relation of a system of Frobenioids and its
two-step factorization.  This is the gluing-composition consumer of
IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystemGluing

variable {iota : Type u} {system : FrobenioidSystem iota}

/-- The relation of the composite gluing. -/
def compRelation (left right : FrobenioidSystemGluing system)
    (source target : iota) : Prop :=
  (left.comp right).relation source target

theorem compRelation_iff (left right : FrobenioidSystemGluing system)
    (source target : iota) :
    compRelation left right source target ↔
      exists middle, left.relation source middle ∧ right.relation middle target :=
  Iff.rfl

end FrobenioidSystemGluing

#check FrobenioidSystemGluing.compRelation
#check FrobenioidSystemGluing.compRelation_iff

end Iut
