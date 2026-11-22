/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemConstant

/-!
# Consumer: axioms and base categories of a constant system

Each component of a constant system has the same Definition 1.3 axiom package
and base category as the single presentation.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota : Type u}

noncomputable def constantAxiomsConsumer
    (presentation : FrobenioidPresentation.{u}) (iota : Type u) (index : iota) :
    (presentation).preFrobenioid.FrobenioidAxioms :=
  presentation.axioms

@[simp] theorem constantAxiomsConsumer_eq
    (presentation : FrobenioidPresentation.{u}) (iota : Type u) (index : iota) :
    constantAxiomsConsumer presentation iota index = presentation.axioms :=
  rfl

noncomputable def constantBaseCategoryConsumer
    (presentation : FrobenioidPresentation.{u}) (iota : Type u) (index : iota) :
    CategoryTheory.Cat.{u, u} :=
  (constant presentation iota).baseCategory index

@[simp] theorem constantBaseCategoryConsumer_eq
    (presentation : FrobenioidPresentation.{u}) (iota : Type u) (index : iota) :
    constantBaseCategoryConsumer presentation iota index =
      presentation.baseCategory :=
  rfl

end FrobenioidSystem

#check FrobenioidSystem.constantAxiomsConsumer
#check FrobenioidSystem.constantBaseCategoryConsumer

end Iut
