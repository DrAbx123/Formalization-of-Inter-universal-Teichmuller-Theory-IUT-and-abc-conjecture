/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Iut.Foundations.SourceFiniteStageModelFrobenioid

/-!
# Place/label presentation family of the finite-stage model

A family of genuine `FrobenioidPresentation`s indexed by finite place and
label.  This is the self-contained family part of IUTchI, Definition 6.13,
(i).
-/

open CategoryTheory

namespace Iut

universe u

namespace SourceFrobenioidSystem

variable {K : Type u} [Field K] [NumberField K]

/-- Place/label presentation family. -/
noncomputable def stageLabeledPresentationFamily
    (Label : Type u) :
    (NumberField.FinitePlace K × Label) -> FrobenioidPresentation.{u} :=
  fun index =>
    SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1

@[simp] theorem stageLabeledPresentationFamily_apply
    (Label : Type u) (index : NumberField.FinitePlace K × Label) :
    stageLabeledPresentationFamily (K := K) Label index =
      SourceFinitePlaceReconstruction.stageModelFrobenioidPresentation index.1 :=
  rfl

#check stageLabeledPresentationFamily
#check stageLabeledPresentationFamily_apply

end SourceFrobenioidSystem
end Iut
