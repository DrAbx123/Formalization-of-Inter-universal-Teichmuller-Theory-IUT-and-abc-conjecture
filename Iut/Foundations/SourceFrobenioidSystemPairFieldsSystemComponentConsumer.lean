/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemFieldsConsumer

/-!
# Consumer: components of the system assembled from pair fields

Bundles presentation, base category, connectedness, and axioms at a Bool index
of the actual system assembled from `PairFields`.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

structure PairSystemComponent (fields : PairFields) (index : Bool) where
  presentation : FrobenioidPresentation.{0}
  base : CategoryTheory.Cat.{0, 0}
  base_eq : base = presentation.baseCategory
  connected : CategoryTheory.IsConnected base
  axioms : presentation.preFrobenioid.FrobenioidAxioms

noncomputable def toSystemComponent
    (fields : PairFields) (index : Bool) :
    PairSystemComponent fields index where
  presentation := (PairFields.toFrobenioidSystem fields).presentation index
  base := systemBaseFamily fields index
  base_eq := rfl
  connected := systemBaseFamily_isConnected fields index
  axioms := fields.axioms index

end PairFields

#check PairFields.PairSystemComponent
#check PairFields.toSystemComponent

end FrobenioidSystem
end Iut
