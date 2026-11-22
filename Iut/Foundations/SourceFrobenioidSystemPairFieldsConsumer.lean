/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairAxiomsFamilyConsumer
import Iut.Foundations.SourceFrobenioidSystemPairBaseFamilyConsumer

/-!
# Consumer: fields of the two-component system

Bundles the Bool-indexed presentation, base-category, connectedness, and
axiom families of the pair system.
-/

open CategoryTheory

universe u

namespace Iut

namespace FrobenioidSystem

structure PairFields where
  presentation : Bool -> FrobenioidPresentation.{0}
  base : Bool -> CategoryTheory.Cat.{0, 0}
  base_eq : forall index, base index = (presentation index).baseCategory
  connected : forall index, CategoryTheory.IsConnected (base index)
  axioms : forall index, (presentation index).preFrobenioid.FrobenioidAxioms

namespace PairFields

noncomputable def ofPair
    (left right : FrobenioidPresentation.{0}) : PairFields where
  presentation := pairPresentation left right
  base := pairBaseFamily left right
  base_eq := fun index => rfl
  connected := fun index => pairBaseFamily_isConnected left right index
  axioms := fun index => pairAxiomsFamily left right index

end PairFields

#check PairFields
#check PairFields.ofPair

end FrobenioidSystem
end Iut
