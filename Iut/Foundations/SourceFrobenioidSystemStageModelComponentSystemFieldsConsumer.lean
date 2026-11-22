/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFrobenioidSystemStageModelComponentSystemBaseFamilyConsumer
import Iut.Foundations.SourceFrobenioidSystemStageModelComponentSystemPresentationFamilyConsumer
import Iut.Foundations.SourceFrobenioidSystemStageModelComponentSystemAxiomsFamilyConsumer

/-!
# Consumer: fields of the component system of Frobenioids

Bundles the presentation family, base-category family, connectedness, and
axiom family of the assembled place/label system.
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

structure StageModelComponentSystemFields (Label : Type u) where
  presentation : (NumberField.FinitePlace K × Label) -> FrobenioidPresentation.{u}
  base : (NumberField.FinitePlace K × Label) -> CategoryTheory.Cat.{u, u}
  base_eq : forall index, base index = (presentation index).baseCategory
  connected : forall index, CategoryTheory.IsConnected (base index)
  axioms : forall index, (presentation index).preFrobenioid.FrobenioidAxioms

namespace StageModelComponentSystemFields

noncomputable def ofComponents (Label : Type u) :
    StageModelComponentSystemFields (K := K) Label where
  presentation := stageModelComponentSystemPresentationFamily (K := K) Label
  base := stageModelComponentSystemBaseFamily (K := K) Label
  base_eq := fun index =>
    (stageModelPresentationComponentFamily (K := K) Label index).base_eq
  connected := fun index => by
    simpa [stageModelComponentSystemBaseFamily] using
      (stageModelPresentationComponentFamily (K := K) Label index).connected
  axioms := fun index =>
    stageModelComponentSystemAxiomsFamily (K := K) Label index

end StageModelComponentSystemFields

#check StageModelComponentSystemFields
#check StageModelComponentSystemFields.ofComponents

end SourceFrobenioidSystem
end Iut
