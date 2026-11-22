/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemConstantAxiomsConsumer

/-!
# Consumer: connectedness of constant-system base categories

Every base category of a constant system is connected, because it is the base
category of the single Frobenioid presentation.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

variable {iota : Type u}

theorem constantBaseCategoryConsumer_isConnected
    (presentation : FrobenioidPresentation.{u}) (iota : Type u) (index : iota) :
    CategoryTheory.IsConnected
      (constantBaseCategoryConsumer presentation iota index) :=
  presentation.baseConnected

#check FrobenioidSystem.constantBaseCategoryConsumer_isConnected

end FrobenioidSystem
end Iut
