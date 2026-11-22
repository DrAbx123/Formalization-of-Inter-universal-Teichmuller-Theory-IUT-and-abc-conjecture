/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemGluing

/-!
# Consumer: trivial gluing of a system of Frobenioids

Exposes the identity gluing relation and its identity equivalences.  This is
the base case used by gluing consumers of IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystemGluing

variable {iota : Type u} {system : FrobenioidSystem iota}

/-- The identity gluing relation. -/
def trivialRelation (system : FrobenioidSystem iota) (source target : iota) : Prop :=
  (FrobenioidSystemGluing.trivial system).relation source target

theorem trivialRelation_iff (system : FrobenioidSystem iota) (source target : iota) :
    trivialRelation system source target ↔ source = target :=
  Iff.rfl

/-- The identity equivalence for equal indices. -/
def trivialEquivalence (system : FrobenioidSystem iota)
    {source target : iota} (related : trivialRelation system source target) :
    CategoryTheory.Equivalence
      (system.presentation source).carrier
      (system.presentation target).carrier :=
  (FrobenioidSystemGluing.trivial system).equivalence related

@[simp] theorem trivialEquivalence_eq (system : FrobenioidSystem iota)
    {source target : iota} (related : trivialRelation system source target) :
    trivialEquivalence system related =
      (FrobenioidSystemGluing.trivial system).equivalence related :=
  rfl

end FrobenioidSystemGluing

#check FrobenioidSystemGluing.trivialRelation
#check FrobenioidSystemGluing.trivialRelation_iff
#check FrobenioidSystemGluing.trivialEquivalence

end Iut
