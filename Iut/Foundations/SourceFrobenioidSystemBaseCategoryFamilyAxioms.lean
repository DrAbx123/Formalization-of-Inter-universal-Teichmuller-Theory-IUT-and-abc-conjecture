/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Base-category family and Frobenioid axioms

Each base category of the place/label model family comes from a genuine
Frobenioid presentation satisfying the full Definition 1.3 axiom package.
This is a self-contained piece of IUTchI, Definition 6.13, (i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

/-- Base-category family indexed by place and label. -/
noncomputable def stageBaseCategoryFamily (Label : Type u) :
    (NumberField.FinitePlace K × Label) -> CategoryTheory.Cat.{u, u} :=
  fun index =>
    (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
      |>.baseCategory

/-- Each component is a genuine Frobenioid presentation. -/
noncomputable def stageBaseCategoryFamily_axioms
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
      |>.preFrobenioid.FrobenioidAxioms :=
  (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1).axioms

/-- Each base category is connected. -/
theorem stageBaseCategoryFamily_isConnected
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.IsConnected (stageBaseCategoryFamily (K := K) Label index) :=
  (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
    |>.baseConnected

#check stageBaseCategoryFamily
#check stageBaseCategoryFamily_axioms
#check stageBaseCategoryFamily_isConnected

end SourceFrobenioidSystem
end Iut
