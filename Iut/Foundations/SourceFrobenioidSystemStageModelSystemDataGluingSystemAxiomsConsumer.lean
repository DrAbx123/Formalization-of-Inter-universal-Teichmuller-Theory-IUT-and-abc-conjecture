/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelSystemDataGluingSystemConsumer

/-!
# Consumer: Frobenioid axioms from the system+gluing data

Exposes the component Definition 1.3 axiom package from a
`StageModelSystemDataGluing` via its extracted system of Frobenioids.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]
variable {Label : Type u} {G : Type u} [Group G]

namespace StageModelSystemDataGluing

noncomputable def systemAxiomsConsumer
    (data : StageModelSystemDataGluing (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    ((data.toFrobenioidSystem).presentation index).preFrobenioid.FrobenioidAxioms :=
  ((data.toFrobenioidSystem).presentation index).axioms

@[simp] theorem systemAxiomsConsumer_eq
    (data : StageModelSystemDataGluing (K := K) Label G)
    (index : NumberField.FinitePlace K × Label) :
    data.systemAxiomsConsumer index =
      (data.system.presentation index).axioms :=
  rfl

end StageModelSystemDataGluing

#check StageModelSystemDataGluing.systemAxiomsConsumer
#check StageModelSystemDataGluing.systemAxiomsConsumer_eq

end SourceFrobenioidSystem
end Iut
