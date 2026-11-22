/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemOptionConsumer

/-!
# Consumer: axioms of an Option-extended system

Each old component and the newly adjoined component carry their Definition
1.3 axiom packages.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota : Type u}

noncomputable def optionAxiomsConsumer
    (system : FrobenioidSystem iota)
    (presentation : FrobenioidPresentation.{u}) (index : Option iota) :
    (optionPresentation system presentation index).preFrobenioid.FrobenioidAxioms :=
  (optionPresentation system presentation index).axioms

@[simp] theorem optionAxiomsConsumer_none
    (system : FrobenioidSystem iota)
    (presentation : FrobenioidPresentation.{u}) :
    optionAxiomsConsumer system presentation none = presentation.axioms :=
  rfl

@[simp] theorem optionAxiomsConsumer_some
    (system : FrobenioidSystem iota)
    (presentation : FrobenioidPresentation.{u}) (index : iota) :
    optionAxiomsConsumer system presentation (some index) =
      (system.presentation index).axioms :=
  rfl

end FrobenioidSystem

#check FrobenioidSystem.optionAxiomsConsumer
#check FrobenioidSystem.optionAxiomsConsumer_none
#check FrobenioidSystem.optionAxiomsConsumer_some

end Iut
