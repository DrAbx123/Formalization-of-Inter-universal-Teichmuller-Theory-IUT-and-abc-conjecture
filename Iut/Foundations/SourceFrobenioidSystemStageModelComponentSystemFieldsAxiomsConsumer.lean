/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelComponentSystemFieldsSystemConsumer

/-!
# Consumer: axioms of the fields-assembled system

Each component of the system assembled from fields carries its Definition 1.3
axiom package.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u}

namespace StageModelComponentSystemFields

noncomputable def systemAxiomsConsumer
    (fields : StageModelComponentSystemFields (K := K) Label)
    (index : NumberField.FinitePlace K × Label) :
    ((StageModelComponentSystemFields.toFrobenioidSystem fields).presentation index)
      |>.preFrobenioid.FrobenioidAxioms :=
  fields.axioms index

@[simp] theorem systemAxiomsConsumer_eq
    (fields : StageModelComponentSystemFields (K := K) Label)
    (index : NumberField.FinitePlace K × Label) :
    StageModelComponentSystemFields.systemAxiomsConsumer fields index =
      fields.axioms index :=
  rfl

end StageModelComponentSystemFields

#check StageModelComponentSystemFields.systemAxiomsConsumer
#check StageModelComponentSystemFields.systemAxiomsConsumer_eq

end SourceFrobenioidSystem
end Iut
