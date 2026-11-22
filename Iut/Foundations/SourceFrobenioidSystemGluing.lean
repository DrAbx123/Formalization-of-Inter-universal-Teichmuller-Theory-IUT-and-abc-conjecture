/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystem

/-!
# Minimal gluing data for a system of Frobenioids

IUTchI, Definition 6.13, (i), glues the system of Frobenioids by full
poly-isomorphisms.  This file records the minimal data-level counterpart:
a relation on the index set and, for every related pair, an actual
categorical equivalence between the carrier categories of the corresponding
Frobenioid presentations.

No coherence proofs and no arbitrary `Prop` fields are added here; the
identity gluing is provided for every system.  Compatibility of these
equivalences with the Frobenioid structure remains future work.
-/

open CategoryTheory

namespace Iut

universe u

/-- Equivalence of categories induced by an equality of Cat objects. -/
noncomputable def eqToEquivalenceCat
    {C D : CategoryTheory.Cat.{u, u}} (h : C = D) : C ≌ D := by
  cases h
  exact CategoryTheory.Equivalence.refl

/-- Minimal gluing data between the components of a Frobenioid system. -/
structure FrobenioidSystemGluing {iota : Type u}
    (system : FrobenioidSystem iota) where
  relation : iota -> iota -> Prop
  equivalence :
    forall {source target : iota}, relation source target ->
      CategoryTheory.Equivalence
        (system.presentation source).carrier
        (system.presentation target).carrier

namespace FrobenioidSystemGluing

variable {iota : Type u} {system : FrobenioidSystem iota}

/-- The identity gluing: equality of indices, with the identity equivalence. -/
noncomputable def trivial (system : FrobenioidSystem iota) :
    FrobenioidSystemGluing system where
  relation := fun source target => source = target
  equivalence := fun {source target} related =>
    eqToEquivalenceCat
      (congrArg (fun index => (system.presentation index).carrier) related)

end FrobenioidSystemGluing

#check FrobenioidSystemGluing
#check FrobenioidSystemGluing.trivial

end Iut
