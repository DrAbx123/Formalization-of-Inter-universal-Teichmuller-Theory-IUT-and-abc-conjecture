/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystem

/-!
# Constant systems of Frobenioids

A constant family of Frobenioid presentations.  This is the minimal actual
way to build a system from one Frobenioid presentation, and is used as the
identity/trivial component for gluing data.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

/-- The constant system with every component equal to `presentation`. -/
def constant (presentation : FrobenioidPresentation.{u}) (iota : Type u) :
    FrobenioidSystem iota where
  presentation := fun _ => presentation

@[simp] theorem constant_presentation
    (presentation : FrobenioidPresentation.{u}) (iota : Type u) (index : iota) :
    (constant presentation iota).presentation index = presentation :=
  rfl

@[simp] theorem constant_baseCategory
    (presentation : FrobenioidPresentation.{u}) (iota : Type u) (index : iota) :
    (constant presentation iota).baseCategory index = presentation.baseCategory :=
  rfl

end FrobenioidSystem

#check FrobenioidSystem.constant
#check FrobenioidSystem.constant_baseCategory

end Iut
