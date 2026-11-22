/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystem

/-!
# Systems from presentation-valued functions

The constructor inverse to `FrobenioidSystem.presentation`: any function from
an index type to `FrobenioidPresentation` gives an actual system of
Frobenioids.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota : Type u}

/-- Build a system from a family of Frobenioid presentations. -/
def ofFun (family : iota -> FrobenioidPresentation.{u}) :
    FrobenioidSystem iota where
  presentation := family

@[simp] theorem ofFun_presentation
    (family : iota -> FrobenioidPresentation.{u}) (index : iota) :
    (ofFun family).presentation index = family index :=
  rfl

@[simp] theorem ofFun_presentation_fun
    (system : FrobenioidSystem iota) :
    ofFun system.presentation = system :=
  rfl

end FrobenioidSystem

#check FrobenioidSystem.ofFun
#check FrobenioidSystem.ofFun_presentation
#check FrobenioidSystem.ofFun_presentation_fun

end Iut
