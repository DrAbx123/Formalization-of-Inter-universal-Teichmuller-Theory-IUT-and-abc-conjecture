/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystem

/-!
# Two-component systems of Frobenioids

The two-element index `Bool` gives a system with exactly two components.
This is the minimal nontrivial place/label system.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

/-- The system with two components. -/
def pair (left right : FrobenioidPresentation.{0}) :
    FrobenioidSystem Bool where
  presentation := fun index =>
    match index with
    | false => left
    | true => right

@[simp] theorem pair_false (left right : FrobenioidPresentation.{0}) :
    (pair left right).presentation false = left :=
  rfl

@[simp] theorem pair_true (left right : FrobenioidPresentation.{0}) :
    (pair left right).presentation true = right :=
  rfl

end FrobenioidSystem

#check FrobenioidSystem.pair
#check FrobenioidSystem.pair_false
#check FrobenioidSystem.pair_true

end Iut
