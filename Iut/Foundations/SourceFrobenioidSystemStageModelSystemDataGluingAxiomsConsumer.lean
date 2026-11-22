/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingFieldsConsumer

/-!
# Consumer: dependent axiom family of place/label system data

Packages the component Definition 1.3 axiom packages as a dependent family.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u} {G : Type u} [Group G]

namespace StageModelSystemDataGluing

/-- Dependent family of component Frobenioid axioms. -/
noncomputable def axiomsFamily
    (data : StageModelSystemDataGluing (K := K) Label G) :
    (index : NumberField.FinitePlace K × Label) ->
      (data.system.presentation index).preFrobenioid.FrobenioidAxioms :=
  fun index => data.axioms index

@[simp] theorem axiomsFamily_apply
    (data : StageModelSystemDataGluing (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    data.axiomsFamily index = data.axioms index :=
  rfl

end StageModelSystemDataGluing

#check StageModelSystemDataGluing.axiomsFamily
#check StageModelSystemDataGluing.axiomsFamily_apply

end SourceFrobenioidSystem
end Iut
