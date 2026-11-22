/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataPresentationConsumer

/-!
# Consumer: dependent axiom family of the place/label system data

Packages the component Definition 1.3 axiom packages as a dependent family.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u}

namespace StageModelSystemData

noncomputable def axiomsFamilyConsumer
    (data : StageModelSystemData (K := K) Label) :
    (index : NumberField.FinitePlace K × Label) ->
      (StageModelSystemData.presentationConsumer data index).preFrobenioid.FrobenioidAxioms :=
  fun index => StageModelSystemData.presentationAxiomsConsumer data index

@[simp] theorem axiomsFamilyConsumer_apply
    (data : StageModelSystemData (K := K) Label)
    (index : NumberField.FinitePlace K × Label) :
    StageModelSystemData.axiomsFamilyConsumer data index =
      StageModelSystemData.presentationAxiomsConsumer data index :=
  rfl

end StageModelSystemData

#check StageModelSystemData.axiomsFamilyConsumer
#check StageModelSystemData.axiomsFamilyConsumer_apply

end SourceFrobenioidSystem
end Iut
