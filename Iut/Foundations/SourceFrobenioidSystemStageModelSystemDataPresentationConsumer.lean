/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemData

/-!
# Consumer: presentations of the place/label system data

Projects the Frobenioid presentation and its Definition 1.3 axiom package at
each place/label index.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u}

namespace StageModelSystemData

noncomputable def presentationConsumer
    (data : StageModelSystemData (K := K) Label)
    (index : NumberField.FinitePlace K × Label) :
    FrobenioidPresentation.{u} :=
  data.presentation index

@[simp] theorem presentationConsumer_eq
    (data : StageModelSystemData (K := K) Label)
    (index : NumberField.FinitePlace K × Label) :
    data.presentationConsumer index = data.presentation index :=
  rfl

noncomputable def presentationAxiomsConsumer
    (data : StageModelSystemData (K := K) Label)
    (index : NumberField.FinitePlace K × Label) :
    (data.presentationConsumer index).preFrobenioid.FrobenioidAxioms :=
  data.axioms index

end StageModelSystemData

#check StageModelSystemData.presentationConsumer
#check StageModelSystemData.presentationAxiomsConsumer

end SourceFrobenioidSystem
end Iut
