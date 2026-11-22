/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Base categories of the finite-stage model family

The base category of each finite-place model Frobenioid is connected.  This
is a self-contained piece of the D-Theta+-ellNF system of base categories
(IUTchI, Definition 6.13, (i)).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

/-- Base category of the model Frobenioid at a finite place. -/
noncomputable def stageBaseCategory (place : NumberField.FinitePlace K) :
    CategoryTheory.Cat.{u, u} :=
  (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation place).baseCategory

theorem stageBaseCategory_isConnected
    (place : NumberField.FinitePlace K) :
    CategoryTheory.IsConnected (stageBaseCategory (K := K) place) :=
  (SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation place).baseConnected

#check stageBaseCategory
#check stageBaseCategory_isConnected

end SourceFrobenioidSystem
end Iut
