/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairAxiomsConsumer

/-!
# Consumer: dependent axiom family of the two-component system

Packages both components' Definition 1.3 axiom packages as a Bool-indexed
dependent family.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

noncomputable def pairAxiomsFamily
    (left right : FrobenioidPresentation.{0}) :
    (index : Bool) ->
      (pairPresentation left right index).preFrobenioid.FrobenioidAxioms :=
  fun index => pairAxiomsConsumer left right index

@[simp] theorem pairAxiomsFamily_apply
    (left right : FrobenioidPresentation.{0}) (index : Bool) :
    pairAxiomsFamily left right index =
      pairAxiomsConsumer left right index :=
  rfl

end FrobenioidSystem

#check FrobenioidSystem.pairAxiomsFamily
#check FrobenioidSystem.pairAxiomsFamily_apply

end Iut
