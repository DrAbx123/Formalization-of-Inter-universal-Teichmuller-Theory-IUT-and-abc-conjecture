/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Place/label system data for the finite-stage model

A single structure packaging, for each place/label component:
* the actual Frobenioid presentation;
* its base category and the definitional equality;
* connectedness of the base category;
* the full Frobenioid axiom package.

This is the self-contained data of the system of Frobenioids and its system
of base categories in IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

/-- Place/label system data of genuine model Frobenioids. -/
structure StageModelSystemData (Label : Type u) where
  presentation :
    (NumberField.FinitePlace K × Label) -> FrobenioidPresentation.{u}
  base :
    (NumberField.FinitePlace K × Label) -> CategoryTheory.Cat.{u, u}
  base_eq :
    forall index, base index = (presentation index).baseCategory
  base_connected :
    forall index, CategoryTheory.IsConnected (base index)
  axioms :
    forall index, (presentation index).preFrobenioid.FrobenioidAxioms

namespace StageModelSystemData

/-- The concrete finite-stage model system data. -/
noncomputable def ofFiniteStage (Label : Type u) :
    StageModelSystemData (K := K) Label where
  presentation := fun index =>
    SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1
  base := fun index =>
    (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
      |>.baseCategory
  base_eq := fun index => rfl
  base_connected := fun index =>
    (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
      |>.baseConnected
  axioms := fun index =>
    (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
      |>.axioms

@[simp] theorem ofFiniteStage_presentation
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    (ofFiniteStage (K := K) Label).presentation index =
      SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1 :=
  rfl

end StageModelSystemData

#check StageModelSystemData
#check StageModelSystemData.ofFiniteStage

end SourceFrobenioidSystem
end Iut
