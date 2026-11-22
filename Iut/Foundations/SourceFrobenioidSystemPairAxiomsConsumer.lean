/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairConsumer

/-!
# Consumer: Frobenioid axioms of the two-component system

Each component of the two-component system carries the full Definition 1.3
axiom package.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

/-- Axioms at a `Bool` index of a pair system. -/
noncomputable def pairAxiomsConsumer
    (left right : FrobenioidPresentation.{0}) (index : Bool) :
    (pairPresentation left right index).preFrobenioid.FrobenioidAxioms :=
  (pairPresentation left right index).axioms

@[simp] theorem pairAxiomsConsumer_false
    (left right : FrobenioidPresentation.{0}) :
    pairAxiomsConsumer left right false = left.axioms :=
  rfl

@[simp] theorem pairAxiomsConsumer_true
    (left right : FrobenioidPresentation.{0}) :
    pairAxiomsConsumer left right true = right.axioms :=
  rfl

end FrobenioidSystem

#check FrobenioidSystem.pairAxiomsConsumer
#check FrobenioidSystem.pairAxiomsConsumer_false
#check FrobenioidSystem.pairAxiomsConsumer_true

end Iut
