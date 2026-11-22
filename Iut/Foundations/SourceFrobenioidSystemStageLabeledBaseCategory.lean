/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Place/label base categories of the finite-stage model family

Each place/label component has a connected base category.  This is a
self-contained instance of the D-Theta+-ellNF system of base categories
(IUTchI, Definition 6.13, (i)).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

/-- Base categories indexed by place and label. -/
noncomputable def stageLabeledBaseCategoryFamily
    (Label : Type u) :
    (NumberField.FinitePlace K × Label) -> CategoryTheory.Cat.{u, u} :=
  fun index =>
    (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
      |>.baseCategory

theorem stageLabeledBaseCategoryFamily_isConnected
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    CategoryTheory.IsConnected
      (stageLabeledBaseCategoryFamily (K := K) Label index) :=
  (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1)
    |>.baseConnected

#check stageLabeledBaseCategoryFamily
#check stageLabeledBaseCategoryFamily_isConnected

end SourceFrobenioidSystem
end Iut
