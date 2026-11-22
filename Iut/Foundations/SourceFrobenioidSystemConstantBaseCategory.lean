/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemConstant
import Iut.Foundations.SourceFrobenioidSystemBaseCategory

/-!
# Base categories of a constant system

The base-category family of a constant system is the constant family of the
base category of the single presentation.  This is the base-category
counterpart of the trivial system construction.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

@[simp] theorem constant_baseCategoryFamily
    (presentation : FrobenioidPresentation.{u}) (iota : Type u) (index : iota) :
    (constant presentation iota).baseCategoryFamily index =
      presentation.baseCategory :=
  rfl

#check FrobenioidSystem.constant_baseCategoryFamily

end FrobenioidSystem
end Iut
