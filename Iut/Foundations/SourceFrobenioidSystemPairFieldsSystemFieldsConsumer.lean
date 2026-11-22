/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemPairFieldsSystemConsumer

/-!
# Consumer: fields of the system assembled from pair fields

Exposes the base-category and axiom families of the actual `FrobenioidSystem`
assembled from `PairFields`.
-/

open CategoryTheory

namespace Iut

namespace FrobenioidSystem

namespace PairFields

noncomputable def systemBaseFamily
    (fields : PairFields) : Bool -> CategoryTheory.Cat.{0, 0} :=
  fun index => (PairFields.toFrobenioidSystem fields).baseCategory index

@[simp] theorem systemBaseFamily_eq (fields : PairFields) (index : Bool) :
    systemBaseFamily fields index = fields.base index :=
  (fields.base_eq index).symm

theorem systemBaseFamily_isConnected (fields : PairFields) (index : Bool) :
    CategoryTheory.IsConnected (systemBaseFamily fields index) := by
  rw [systemBaseFamily_eq]
  exact fields.connected index

noncomputable def systemAxiomsFamily
    (fields : PairFields) :
    (index : Bool) ->
      ((PairFields.toFrobenioidSystem fields).presentation index)
        |>.preFrobenioid.FrobenioidAxioms :=
  fun index => fields.axioms index

end PairFields

#check PairFields.systemBaseFamily
#check PairFields.systemAxiomsFamily

end FrobenioidSystem
end Iut
