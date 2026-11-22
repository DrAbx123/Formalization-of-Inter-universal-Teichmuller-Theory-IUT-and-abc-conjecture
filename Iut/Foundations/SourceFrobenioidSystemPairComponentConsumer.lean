/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairConsumer
import Iut.Foundations.SourceFrobenioidSystemPairAxiomsConsumer
import Iut.Foundations.SourceFrobenioidSystemPairBaseConsumer

/-!
# Consumer: component data of the two-component system

Bundles presentation, base category, connectedness, and axioms at a Bool index.
-/

open CategoryTheory

namespace Iut

universe u

namespace FrobenioidSystem

structure PairComponent (index : Bool) where
  presentation : FrobenioidPresentation.{0}
  base : CategoryTheory.Cat.{0, 0}
  base_eq : base = presentation.baseCategory
  connected : CategoryTheory.IsConnected base
  axioms : presentation.preFrobenioid.FrobenioidAxioms

namespace PairComponent

noncomputable def ofPair
    (left right : FrobenioidPresentation.{0}) (index : Bool) :
    PairComponent index where
  presentation := pairPresentation left right index
  base := pairBaseCategoryConsumer left right index
  base_eq := rfl
  connected := pairBaseCategoryConsumer_isConnected left right index
  axioms := pairAxiomsConsumer left right index

end PairComponent

#check PairComponent
#check PairComponent.ofPair

end FrobenioidSystem
end Iut
