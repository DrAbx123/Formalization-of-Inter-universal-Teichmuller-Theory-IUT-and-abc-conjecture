/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemComponentConsumer

/-!
# Consumer: fields of pair system components

Projects presentation, base category, and axioms from the component bundle.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def componentPresentation
    (fields : PairFields) (index : Bool) : FrobenioidPresentation.{0} :=
  (PairFields.toSystemComponent fields index).presentation

noncomputable def componentBase
    (fields : PairFields) (index : Bool) : CategoryTheory.Cat.{0, 0} :=
  (PairFields.toSystemComponent fields index).base

theorem componentBase_isConnected
    (fields : PairFields) (index : Bool) :
    CategoryTheory.IsConnected (componentBase fields index) :=
  (PairFields.toSystemComponent fields index).connected

noncomputable def componentAxioms
    (fields : PairFields) (index : Bool) :
    (componentPresentation fields index).preFrobenioid.FrobenioidAxioms :=
  (PairFields.toSystemComponent fields index).axioms

end PairFields

#check PairFields.componentPresentation
#check PairFields.componentBase
#check PairFields.componentAxioms

end FrobenioidSystem
end Iut
