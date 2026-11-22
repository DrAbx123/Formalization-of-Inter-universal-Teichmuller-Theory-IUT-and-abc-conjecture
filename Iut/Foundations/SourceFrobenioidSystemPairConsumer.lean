/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPair

/-!
# Consumer: two-component system of Frobenioids

Projects the two components of the minimal nontrivial system.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota : Type u}

/-- The presentation at a `Bool` index of a pair system. -/
noncomputable def pairPresentation
    (left right : FrobenioidPresentation.{0}) (index : Bool) :
    FrobenioidPresentation.{0} :=
  (pair left right).presentation index

@[simp] theorem pairPresentation_false
    (left right : FrobenioidPresentation.{0}) :
    pairPresentation left right false = left :=
  rfl

@[simp] theorem pairPresentation_true
    (left right : FrobenioidPresentation.{0}) :
    pairPresentation left right true = right :=
  rfl

end FrobenioidSystem

#check FrobenioidSystem.pairPresentation
#check FrobenioidSystem.pairPresentation_false
#check FrobenioidSystem.pairPresentation_true

end Iut
